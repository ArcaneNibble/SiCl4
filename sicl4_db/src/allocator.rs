//! Custom slab-based memory allocator
//!
//! This is a custom concurrent slab memory allocator inspired by the
//! [sharded_slab](https://docs.rs/sharded-slab/latest/sharded_slab/implementation/index.html)
//! crate, which is in turn inspired by the
//! [Mimalloc](https://www.microsoft.com/en-us/research/uploads/prod/2019/06/mimalloc-tr-v1.pdf)
//! allocator from Microsoft Research.
//!
//! This code has tighter integration between memory allocation and object locking.
//! Some notes as to why have been written
//! [here](https://arcanenibble.github.io/drafts/parallel-capable-netlist-data-structures-part-2.html)
//! (TODO CHANGE THIS WHEN PUBLISHED).

use std::{
    alloc::{self, Layout},
    cell::Cell,
    fmt::Debug,
    marker::PhantomData,
    mem::{self, size_of, ManuallyDrop, MaybeUninit},
    ptr::{self, addr_of, addr_of_mut},
    sync::atomic::{AtomicPtr, AtomicU64, Ordering},
};

use crate::util::divroundup;

/// Absolute maximum number of threads that can be supported.
///
/// The reason that this is not dynamic is because the "root" state needs
/// to store per-thread data and then hand out references to it.
/// If this were stored in a `Vec` then reallocating the backing store
/// will invalidate the references that have been handed out.
/// This can be replaced with something like the `elsa` crate if necessary.
///
/// Currently limited to 64 so that a u64 atomic bitfield can be used
pub const MAX_THREADS: usize = 64;
const _: () = assert!(MAX_THREADS <= 64);
/// log2 of the size of a segment containing pages
const SEGMENT_SHIFT: usize = 22; // 4 M
/// Size in bytes of a segment containing pages
const SEGMENT_SZ: usize = 1 << SEGMENT_SHIFT;
/// [Layout] of an appropriately-aligned segment (aligned to its size)
const SEGMENT_LAYOUT: Layout = match Layout::from_size_align(SEGMENT_SZ, SEGMENT_SZ) {
    Ok(x) => x,
    Err(_) => panic!("Invalid SEGMENT_SZ"),
};
/// log2 of the size of a page within a segment
const ALLOC_PAGE_SHIFT: usize = 16; // 64 K
/// Size in bytes of a page within a segment
const ALLOC_PAGE_SZ: usize = 1 << ALLOC_PAGE_SHIFT;
/// The number of allocator pages that fit within a segment
const PAGES_PER_SEG: usize = SEGMENT_SZ / ALLOC_PAGE_SZ;

/// Remove this when Layout::pad_to_align is stably const
const fn pad_to_align(inp: Layout) -> Layout {
    // mostly cribbed from https://doc.rust-lang.org/src/core/alloc/layout.rs.html
    // except overflow is ignored
    let align = inp.align();
    let len = inp.size();
    let len_rounded_up = (len + align - 1) & !(align - 1);
    match Layout::from_size_align(len_rounded_up, align) {
        Ok(x) => x,
        Err(_) => unreachable!(),
    }
}

/// Calculate the maximum number of the given layout that can fit into `tot_sz`
const fn num_that_fits(layout: Layout, tot_sz: usize) -> usize {
    let layout = pad_to_align(layout);
    tot_sz / layout.size()
}

#[derive(Debug)]
/// Slab allocator root object
pub struct SlabRoot<'arena, T> {
    /// Bitfield, where a `1` bit in position `n` indicates that
    /// a [SlabThreadShard] has been handed out for the nth entry of
    /// [per_thread_state](Self::per_thread_state)
    /// (and it hasn't been dropped yet)
    thread_inuse: AtomicU64,
    /// Actual storage for per-thread data
    per_thread_state: [SlabPerThreadState<'arena, T>; MAX_THREADS],
    /// Ensure `'arena` lifetime is invariant
    _p: PhantomData<Cell<&'arena ()>>,
}
// safety: we carefully use atomic operations on thread_inuse
unsafe impl<'arena, T> Sync for SlabRoot<'arena, T> {}

impl<'arena, T> SlabRoot<'arena, T> {
    /// Allocate a new root object for a slab memory allocator
    pub fn new() -> Self {
        // safety: standard array per-element init, where a MaybeUninit doesn't require init
        let mut per_thread_state: [MaybeUninit<SlabPerThreadState<T>>; MAX_THREADS] =
            unsafe { MaybeUninit::uninit().assume_init() };

        // use the trick from the shared-arena crate
        // (except corrected, see https://github.com/sebastiencs/shared-arena/issues/6)
        // in order to push the safety requirement down to SlabPerThreadState::init
        for i in 0..MAX_THREADS {
            let _ = SlabPerThreadState::init(&mut per_thread_state[i], i as u64);
        }

        Self {
            thread_inuse: AtomicU64::new(0),
            per_thread_state: unsafe { mem::transmute(per_thread_state) },
            _p: PhantomData,
        }
    }

    /// Get a handle on one per-thread shard of the slab
    ///
    /// Panics if [MAX_THREADS] is reached
    pub fn new_thread(&'arena self) -> SlabThreadShard<'arena, T> {
        let allocated_tid;
        // TODO: relax ordering
        let mut old_inuse = self.thread_inuse.load(Ordering::SeqCst);
        loop {
            let next_tid = old_inuse.trailing_ones();
            if next_tid as usize >= MAX_THREADS {
                panic!("No more threads allowed!");
            }
            let new_inuse = old_inuse | (1 << next_tid);
            match self.thread_inuse.compare_exchange_weak(
                old_inuse,
                new_inuse,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => {
                    allocated_tid = next_tid as usize;
                    break;
                }
                Err(x) => {
                    old_inuse = x;
                }
            }
        }

        let thread_state = &self.per_thread_state[allocated_tid];
        let root_ptr = addr_of!(thread_state.root) as *mut Option<&'arena SlabRoot<'arena, T>>;
        unsafe {
            // safety: current thread now owns this slice of per_thread_state exclusively
            (*root_ptr) = Some(self);
        }
        SlabThreadShard(thread_state)
    }
}

#[derive(Debug)]
/// Slab allocator per-thread state (actual contents)
pub struct SlabPerThreadState<'arena, T> {
    /// Identifies this thread
    ///
    /// Current impl: bit position in the [SlabRoot::thread_inuse] bitfield
    tid: u64,
    /// Pointer to the [SlabRoot] this belongs to
    ///
    /// Can be removed if `offset_of!` gets stabilized
    root: Option<&'arena SlabRoot<'arena, T>>,
    /// Pointer to segment list (used for global ops) TODO
    segments: Cell<Option<&'arena SlabSegmentHdr<'arena, T>>>,
    /// Pointer to head of (non-full, TODO) page list
    pages: Cell<Option<&'arena SlabSegmentPageMeta<'arena, T>>>,
    /// Ensure `'arena` lifetime is invariant
    _p: PhantomData<Cell<&'arena ()>>,
    // XXX
    _p2: PhantomData<T>,
}
// safety: we carefully use atomic operations on FIXME,
// and everything else is owned by one specific thread
// (which is guarded by SlabRoot::thread_inuse)
unsafe impl<'arena, T> Sync for SlabPerThreadState<'arena, T> {}

impl<'arena, T> SlabPerThreadState<'arena, T> {
    /// Initialize state
    pub fn init(self_: &mut MaybeUninit<Self>, tid: u64) -> &mut Self {
        unsafe {
            let p = self_.as_mut_ptr();
            (*p).tid = tid;
            (*p).root = None;
            (*p).segments = Cell::new(None);
            (*p).pages = Cell::new(None);
            // safety: we initialized everything
            &mut *p
        }
    }

    /// Allocate a new segment, link it into segments list,
    /// and make it the head of the pages list
    fn new_seg(&'arena self) {
        let new_seg = SlabSegmentHdr::<'arena, T>::alloc_new_seg(self.tid);
        let old_seg_head = self.segments.take();
        let new_seg = unsafe {
            (*new_seg).next = old_seg_head;
            &*new_seg
        };
        self.segments.set(Some(new_seg));
        self.pages.set(Some(&new_seg.pages[0]));
    }

    /// Allocation slow path
    ///
    /// Returns a block, which must be free and ready for use
    fn alloc_slow(&'arena self) -> &'arena SlabFreeBlock<'arena> {
        let mut page = self.pages.get().unwrap();
        loop {
            page.collect_free_lists();
            if page.this_free_list.get().is_some() {
                return page.this_free_list.get().unwrap();
            } else {
                todo!()
            }
        }
    }

    /// Allocates an object from this shard
    ///
    /// Does *NOT* initialize any of the resulting memory
    pub fn alloc(&'arena self) -> &'arena SlabBlock<'arena, T> {
        // XXX we now have one more branch vs msft
        if self.pages.get().is_none() {
            // need to allocate a new segment
            self.new_seg();
        }

        let page = self.pages.get().unwrap();
        let block = page.this_free_list.get();
        let block = match block {
            Some(x) => x, // fast path
            None => self.alloc_slow(),
        };
        page.this_free_list.set(block.next);
        unsafe {
            // safety: just coercing to a repr(C) union reference
            mem::transmute(block)
        }
    }

    /// Deallocates an object
    ///
    /// Object must be part of this slab, not already be freed,
    /// and no other references may exist after calling free
    pub unsafe fn free(&'arena self, obj: &'arena SlabBlock<'arena, T>) {
        let obj_ptr = obj as *const _ as usize;
        let seg_ptr = obj_ptr & !(SEGMENT_SZ - 1);
        let seg = &*(seg_ptr as *const SlabSegmentHdr<'arena, T>);
        let page_i = (obj_ptr - seg_ptr) >> ALLOC_PAGE_SHIFT;

        // we don't allow freeing null?

        if self.tid == (*seg).owning_tid {
            // local free
            let obj_mut = obj as *const _ as *mut SlabBlock<'arena, T>;
            (*obj_mut).free.next = seg.pages[page_i].local_free_list.get();
            seg.pages[page_i]
                .local_free_list
                .set(Some(mem::transmute(obj)));
        } else {
            // remote free
            // TODO: full list
            let page = &seg.pages[page_i];
            let mut prev_remote_free = page.remote_free_list.load(Ordering::SeqCst);
            loop {
                let obj_mut = obj as *const _ as *mut SlabBlock<'arena, T>;
                (*obj_mut).free.next = Some(&*prev_remote_free);
                match page.remote_free_list.compare_exchange_weak(
                    prev_remote_free,
                    obj_ptr as _,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                ) {
                    Ok(_) => break,
                    Err(x) => prev_remote_free = x,
                }
            }
        }
    }
}

/// Handle to a per-thread shard of an allocator
pub struct SlabThreadShard<'arena, T>(pub &'arena SlabPerThreadState<'arena, T>);

impl<'arena, T> Drop for SlabThreadShard<'arena, T> {
    fn drop(&mut self) {
        let root = self.0.root.unwrap();
        let mask = !(1 << self.0.tid);
        // TODO: relax ordering
        root.thread_inuse.fetch_and(mask, Ordering::SeqCst);
    }
}

/// Header for each (4 M) segment
#[repr(C)]
#[derive(Debug)]
struct SlabSegmentHdr<'arena, T> {
    /// Thread that created this segment and owns its "local" data
    owning_tid: u64,
    /// List of segments (all owned by this thread)
    next: Option<&'arena SlabSegmentHdr<'arena, T>>,
    /// Metadata for each page within the segment
    pages: [SlabSegmentPageMeta<'arena, T>; PAGES_PER_SEG],
    _p: PhantomData<T>,
}
// safety: we carefully use atomic operations on FIXME,
// and everything else is owned by one specific thread
// (which is guarded by SlabRoot::thread_inuse)
unsafe impl<'arena, T> Sync for SlabSegmentHdr<'arena, T> {}

impl<'arena, T> SlabSegmentHdr<'arena, T> {
    pub fn alloc_new_seg(owning_tid: u64) -> *mut Self {
        unsafe {
            let seg = alloc::alloc_zeroed(SEGMENT_LAYOUT) as *mut Self;
            (*seg).owning_tid = owning_tid;

            for i in 0..PAGES_PER_SEG {
                SlabSegmentPageMeta::init_page(addr_of_mut!((*seg).pages[i]), seg, i);
                if i != PAGES_PER_SEG - 1 {
                    let next_page_meta_ptr = addr_of_mut!((*seg).pages[i + 1]);
                    // reborrowing is safe because we *never* make &mut
                    (*seg).pages[i].next_page = Some(&*next_page_meta_ptr);
                }
            }

            // safety: we initialized everything
            seg
        }
    }

    #[inline]
    pub fn get_hdr_rounded_sz() -> usize {
        let t_layout = Layout::new::<SlabBlock<T>>();
        let seg_hdr_size = size_of::<SlabSegmentHdr<T>>();
        let rounded_seg_hdr_sz = divroundup(seg_hdr_size, t_layout.align()) * t_layout.align();
        rounded_seg_hdr_sz
    }

    #[inline]
    pub fn get_addr_of_block(self_: *const Self, page_i: usize, block_i: usize) -> *const u8 {
        assert!(page_i < PAGES_PER_SEG);
        let start_unusable = if page_i == 0 {
            Self::get_hdr_rounded_sz()
        } else {
            0
        };
        let start_offs = page_i * ALLOC_PAGE_SZ + start_unusable;
        let num_objects = num_that_fits(
            Layout::new::<SlabBlock<T>>(),
            ALLOC_PAGE_SZ - start_unusable,
        );
        assert!(block_i < num_objects);
        let t_layout_padded = Layout::new::<SlabBlock<T>>().pad_to_align();
        let tot_offs = start_offs + block_i * t_layout_padded.size();
        let seg_ptr = self_ as *const u8;
        debug_assert!(tot_offs <= SEGMENT_SZ);
        unsafe {
            // safety: we checked all the bounds
            seg_ptr.offset(tot_offs as isize)
        }
    }
}

/// Metadata for each (64 K) page.
///
/// Note that this is not stored *in* the page, but in the segment header.
#[repr(C)]
#[derive(Debug)]
struct SlabSegmentPageMeta<'arena, T> {
    /// Linked list of pages
    next_page: Option<&'arena SlabSegmentPageMeta<'arena, T>>,
    /// List that we allocate from in the fast path
    this_free_list: Cell<Option<&'arena SlabFreeBlock<'arena>>>,
    /// List that we free to from the same thread
    local_free_list: Cell<Option<&'arena SlabFreeBlock<'arena>>>,
    /// List that other threads free onto
    remote_free_list: AtomicPtr<SlabFreeBlock<'arena>>,
    _p: PhantomData<T>, // FIXME what does "covariant (with drop check)" mean?
}
// safety: we carefully use atomic operations on FIXME,
// and everything else is owned by one specific thread
// (which is guarded by SlabRoot::thread_inuse)
unsafe impl<'arena, T> Sync for SlabSegmentPageMeta<'arena, T> {}

impl<'arena, T> SlabSegmentPageMeta<'arena, T> {
    pub unsafe fn init_page(
        self_: *mut Self,
        seg_ptr: *const SlabSegmentHdr<'arena, T>,
        page_i: usize,
    ) {
        // XXX makes assumptions about niche optimization and layout of Option<&_>

        // don't need to init much of the meta, but here we set up the free chain of the blocks themselves
        let start_unusable = if page_i == 0 {
            SlabSegmentHdr::<T>::get_hdr_rounded_sz()
        } else {
            0
        };
        let num_objects = num_that_fits(
            Layout::new::<SlabBlock<T>>(),
            ALLOC_PAGE_SZ - start_unusable,
        );

        for block_i in 0..(num_objects - 1) {
            let block_ptr = SlabSegmentHdr::get_addr_of_block(seg_ptr, page_i, block_i);
            let next_block_ptr = SlabSegmentHdr::get_addr_of_block(seg_ptr, page_i, block_i + 1);
            let block_ptr = block_ptr as *mut SlabBlock<'arena, T>;
            let next_block_ptr = next_block_ptr as *mut SlabFreeBlock<'arena>;

            (*block_ptr).free = SlabFreeBlock {
                next: Some(&*next_block_ptr),
            };
        }

        let block_0_ptr = SlabSegmentHdr::get_addr_of_block(seg_ptr, page_i, 0) as *const _;
        (*self_).this_free_list.set(Some(&*block_0_ptr));
    }

    pub fn collect_free_lists(&'arena self) {
        // this thread
        debug_assert!(self.this_free_list.get().is_none());
        let mut our_free_list = self.local_free_list.take();

        // other threads
        let mut prev_remote_free = self.remote_free_list.load(Ordering::SeqCst);
        loop {
            match self.remote_free_list.compare_exchange_weak(
                prev_remote_free,
                ptr::null_mut(),
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => break,
                Err(x) => prev_remote_free = x,
            }
        }

        if !prev_remote_free.is_null() {
            // append to end of our free list
            if our_free_list.is_none() {
                // only remote free, none of ours
                self.this_free_list.set(Some(unsafe {
                    // safety: these blocks should definitely belong to our allocation
                    // assuming we didn't mess up
                    &*prev_remote_free
                }));
            } else {
                while our_free_list.unwrap().next.is_some() {
                    our_free_list = our_free_list.unwrap().next;
                }
                unsafe {
                    // safety: these blocks should definitely belong to our allocation
                    // assuming we didn't mess up. we can't data race on next because
                    // current thread owns all of the local free list
                    let next = addr_of!(our_free_list.unwrap().next);
                    *(next as *mut _) = Some(&*prev_remote_free);
                }
                self.this_free_list.set(our_free_list);
            }
        } else {
            self.this_free_list.set(our_free_list);
        }
    }
}

/// A slab block (used to ensure size/align for free chain)
#[repr(C)]
pub union SlabBlock<'arena, T> {
    free: SlabFreeBlock<'arena>,
    alloced: ManuallyDrop<MaybeUninit<T>>,
}

/// Contents of a slab block when it is free (i.e. free chain)
#[repr(C)]
#[derive(Debug, Clone, Copy)]
struct SlabFreeBlock<'arena> {
    next: Option<&'arena SlabFreeBlock<'arena>>,
}

/// Wrapped payload type, additionally containing a rwlock and generation counter
/// (for preventing ABA problem)
#[repr(C)]
#[derive(Debug)]
struct SlabPayloadWithLock<T> {
    /// - Low 8 bits = rwlock
    ///     - 0 = not locked
    ///     - !0 = write locked
    ///     - else contains `n - 1` readers
    /// - High bits = generation counter
    // NOTE: current impl restricts MAX_THREADS to never be more than 253
    lock_and_generation: AtomicU64,
    /// Inner data
    payload: T,
}

#[cfg(test)]
mod tests {
    use std::{alloc::Layout, cell::UnsafeCell, sync::atomic::Ordering};

    use crate::util::_debug_hexdump;

    use super::*;

    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}

    #[test]
    fn test_num_that_fits() {
        assert_eq!(num_that_fits(Layout::new::<u32>(), 256), 256 / 4);
        #[repr(align(4))]
        struct WithPadding(u8);
        assert_eq!(num_that_fits(Layout::new::<WithPadding>(), 256), 256 / 4);
    }

    #[test]
    fn ensure_slab_root_send_sync() {
        assert_send::<SlabRoot<'_, UnsafeCell<u8>>>();
        assert_sync::<SlabRoot<'_, UnsafeCell<u8>>>();
    }

    #[test]
    fn ensure_thread_shard_send() {
        assert_send::<SlabThreadShard<'_, UnsafeCell<u8>>>();
    }

    #[test]
    fn slab_root_new_thread() {
        let slab = SlabRoot::<u8>::new();

        let shard1 = slab.new_thread();
        assert_eq!(slab.thread_inuse.load(Ordering::SeqCst), 0b1);
        unsafe {
            assert_eq!(
                slab.per_thread_state.as_ptr().offset(0),
                shard1.0 as *const _
            );
        }
        let shard2 = slab.new_thread();
        assert_eq!(slab.thread_inuse.load(Ordering::SeqCst), 0b11);
        unsafe {
            assert_eq!(
                slab.per_thread_state.as_ptr().offset(1),
                shard2.0 as *const _
            );
        }

        // drop the lower one
        drop(shard1);
        assert_eq!(slab.thread_inuse.load(Ordering::SeqCst), 0b10);

        // this should allocate in its place
        let shard1_2 = slab.new_thread();
        assert_eq!(slab.thread_inuse.load(Ordering::SeqCst), 0b11);
        unsafe {
            assert_eq!(
                slab.per_thread_state.as_ptr().offset(0),
                shard1_2.0 as *const _
            );
        }
    }

    #[test]
    #[ignore = "not automated, human eye verified"]
    fn slab_seg_init() {
        let x = SlabSegmentHdr::<u8>::alloc_new_seg(0);
        unsafe {
            print!("{}", _debug_hexdump(x as *const u8, SEGMENT_SZ).unwrap());
        }
    }

    #[test]
    fn slab_pointer_manip_check() {
        let x = SlabSegmentHdr::<u8>::alloc_new_seg(0);
        // we have min sz and align of 8

        // first object
        assert_eq!(
            SlabSegmentHdr::get_addr_of_block(x, 0, 0) as usize,
            (x as usize) + SlabSegmentHdr::<u8>::get_hdr_rounded_sz()
        );
        assert_eq!(
            SlabSegmentHdr::get_addr_of_block(x, 1, 0) as usize,
            (x as usize) + ALLOC_PAGE_SZ
        );
        assert_eq!(
            SlabSegmentHdr::get_addr_of_block(x, 2, 0) as usize,
            (x as usize) + ALLOC_PAGE_SZ * 2
        );
        assert_eq!(
            SlabSegmentHdr::get_addr_of_block(x, 63, 0) as usize,
            (x as usize) + ALLOC_PAGE_SZ * 63
        );

        // one object in
        assert_eq!(
            SlabSegmentHdr::get_addr_of_block(x, 0, 1) as usize,
            (x as usize) + SlabSegmentHdr::<u8>::get_hdr_rounded_sz() + 8
        );
        assert_eq!(
            SlabSegmentHdr::get_addr_of_block(x, 1, 1) as usize,
            (x as usize) + ALLOC_PAGE_SZ + 8
        );
        assert_eq!(
            SlabSegmentHdr::get_addr_of_block(x, 2, 1) as usize,
            (x as usize) + ALLOC_PAGE_SZ * 2 + 8
        );
        assert_eq!(
            SlabSegmentHdr::get_addr_of_block(x, 63, 1) as usize,
            (x as usize) + ALLOC_PAGE_SZ * 63 + 8
        );
    }

    #[test]
    fn slab_basic_single_thread_alloc() {
        let alloc = SlabRoot::<u8>::new();
        let thread_shard = alloc.new_thread();
        let obj_1 = thread_shard.0.alloc();
        let obj_2 = thread_shard.0.alloc();
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        assert_eq!(obj_1 as *const _ as usize + 8, obj_2 as *const _ as usize);

        unsafe { thread_shard.0.free(obj_2) };
        unsafe { thread_shard.0.free(obj_1) };

        unsafe {
            let seg = thread_shard.0.segments.get().unwrap();
            assert_eq!(
                seg.pages[0].local_free_list.get().unwrap() as *const _ as usize,
                obj_1 as *const _ as usize
            );
            // XXX this makes an awful pointer/usize cast
            assert_eq!(
                *(seg.pages[0].local_free_list.get().unwrap() as *const _ as *const usize),
                obj_2 as *const _ as usize
            );
        }
    }

    #[test]
    fn slab_basic_fake_remote_free() {
        let alloc = SlabRoot::<u8>::new();
        let thread_shard_0 = alloc.new_thread();
        let obj_1 = thread_shard_0.0.alloc();
        let obj_2 = thread_shard_0.0.alloc();
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        let thread_shard_1 = alloc.new_thread();
        unsafe { thread_shard_1.0.free(obj_2) };
        unsafe { thread_shard_1.0.free(obj_1) };

        unsafe {
            let seg = thread_shard_0.0.segments.get().unwrap();
            print!(
                "{}",
                _debug_hexdump(seg as *const _ as *const u8, ALLOC_PAGE_SZ).unwrap()
            );

            assert_eq!(
                seg.pages[0].remote_free_list.load(Ordering::SeqCst) as usize,
                obj_1 as *const _ as usize
            );
            // XXX this makes an awful pointer/usize cast
            assert_eq!(
                *(seg.pages[0].remote_free_list.load(Ordering::SeqCst) as *const usize),
                obj_2 as *const _ as usize
            );
        }
    }

    #[test]
    fn slab_test_collect_local() {
        let alloc = SlabRoot::<[u8; 30000]>::new();
        let thread_shard = alloc.new_thread();
        let obj_1 = thread_shard.0.alloc();
        let obj_2 = thread_shard.0.alloc();
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        unsafe { thread_shard.0.free(obj_1) };
        unsafe { thread_shard.0.free(obj_2) };

        let obj_1_2nd_try = thread_shard.0.alloc();
        let obj_2_2nd_try = thread_shard.0.alloc();
        println!("Allocated obj 1 again {:?}", obj_1_2nd_try as *const _);
        println!("Allocated obj 2 again {:?}", obj_2_2nd_try as *const _);

        assert_eq!(
            obj_1_2nd_try as *const _ as usize,
            obj_2 as *const _ as usize
        );
        assert_eq!(
            obj_2_2nd_try as *const _ as usize,
            obj_1 as *const _ as usize
        );
    }

    #[test]
    fn slab_test_collect_remote() {
        let alloc = SlabRoot::<[u8; 30000]>::new();
        let thread_shard_0 = alloc.new_thread();
        let obj_1 = thread_shard_0.0.alloc();
        let obj_2 = thread_shard_0.0.alloc();
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        let thread_shard_1 = alloc.new_thread();
        unsafe { thread_shard_1.0.free(obj_1) };
        unsafe { thread_shard_1.0.free(obj_2) };

        let obj_1_2nd_try = thread_shard_0.0.alloc();
        let obj_2_2nd_try = thread_shard_0.0.alloc();
        println!("Allocated obj 1 again {:?}", obj_1_2nd_try as *const _);
        println!("Allocated obj 2 again {:?}", obj_2_2nd_try as *const _);

        assert_eq!(
            obj_1_2nd_try as *const _ as usize,
            obj_2 as *const _ as usize
        );
        assert_eq!(
            obj_2_2nd_try as *const _ as usize,
            obj_1 as *const _ as usize
        );
    }

    #[test]
    fn slab_test_collect_both() {
        let alloc = SlabRoot::<[u8; 30000]>::new();
        let thread_shard_0 = alloc.new_thread();
        let obj_1 = thread_shard_0.0.alloc();
        let obj_2 = thread_shard_0.0.alloc();
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        let thread_shard_1 = alloc.new_thread();
        unsafe { thread_shard_0.0.free(obj_1) };
        unsafe { thread_shard_1.0.free(obj_2) };

        let obj_1_2nd_try = thread_shard_0.0.alloc();
        let obj_2_2nd_try = thread_shard_0.0.alloc();
        println!("Allocated obj 1 again {:?}", obj_1_2nd_try as *const _);
        println!("Allocated obj 2 again {:?}", obj_2_2nd_try as *const _);

        assert_eq!(
            obj_1_2nd_try as *const _ as usize,
            obj_1 as *const _ as usize
        );
        assert_eq!(
            obj_2_2nd_try as *const _ as usize,
            obj_2 as *const _ as usize
        );
    }
}
