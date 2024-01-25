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
    cell::{Cell, UnsafeCell},
    fmt::Debug,
    marker::PhantomData,
    mem::{self, size_of, ManuallyDrop, MaybeUninit},
    ops::Deref,
    ptr::{self, addr_of, addr_of_mut},
    sync::atomic::{AtomicPtr, AtomicU64, AtomicUsize, Ordering},
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
pub struct SlabRoot<'arena, T: Send> {
    /// Bitfield, where a `1` bit in position `n` indicates that
    /// a [SlabThreadShard] has been handed out for the nth entry of
    /// [per_thread_state](Self::per_thread_state)
    /// (and it hasn't been dropped yet)
    thread_inuse: AtomicU64,
    /// Actual storage for per-thread data
    per_thread_state: [MaybeUninit<SlabPerThreadState<'arena, T>>; MAX_THREADS],
    /// Indicates whether or not the state has been initialized
    per_thread_state_inited: [Cell<bool>; MAX_THREADS],
    /// Ensure `'arena` lifetime is invariant
    _p: PhantomData<Cell<&'arena ()>>,
}
// safety: we carefully use atomic operations on thread_inuse
unsafe impl<'arena, T: Send> Sync for SlabRoot<'arena, T> {}

impl<'arena, T: Send> SlabRoot<'arena, T> {
    /// Allocate a new root object for a slab memory allocator
    pub fn new() -> Self {
        Self {
            thread_inuse: AtomicU64::new(0),
            per_thread_state: unsafe { MaybeUninit::uninit().assume_init() },
            per_thread_state_inited: std::array::from_fn(|_| Cell::new(false)),
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

        let thread_state = unsafe {
            // safety: current thread now owns this slice of per_thread_state and per_thread_state_inited exclusively
            if !self.per_thread_state_inited[allocated_tid].get() {
                SlabPerThreadState::<'arena, T>::init(
                    self.per_thread_state[allocated_tid].as_ptr() as *mut _,
                    allocated_tid as u64,
                    self,
                );
                self.per_thread_state_inited[allocated_tid].set(true);
            }
            &*self.per_thread_state[allocated_tid].as_ptr()
        };
        SlabThreadShard(thread_state, PhantomData)
    }
}

#[derive(Debug)]
/// Slab allocator per-thread state (actual contents)
pub struct SlabPerThreadState<'arena, T: Send> {
    /// Identifies this thread
    ///
    /// Current impl: bit position in the [SlabRoot::thread_inuse] bitfield
    tid: u64,
    /// Pointer to the [SlabRoot] this belongs to
    ///
    /// Can be removed if `offset_of!` gets stabilized
    root: &'arena SlabRoot<'arena, T>,
    /// Pointer to segment list (used for global ops) TODO
    segments: Cell<&'arena SlabSegmentHdr<'arena, T>>,
    /// Pointer to head of (non-full, TODO) page list
    pages: Cell<&'arena SlabSegmentPageMeta<'arena, T>>,
    /// Pointer to end of (non-full, TODO) page list
    last_page: Cell<&'arena SlabSegmentPageMeta<'arena, T>>,
    /// List of blocks freed by another thread when the containing page was full
    ///
    /// This is an optimization to prevent having to search through many full pages
    thread_delayed_free: AtomicPtr<SlabFreeBlock<'arena>>,
}
// safety: this is a *huge* footgun. this is marked Sync so that it is possible
// for multiple threads to get access to it so that they can access the
// thread delayed free block list. it is *not* otherwise safe.
//
// however, because only a SlabThreadShard can get outside this module,
// the footgun is contained
unsafe impl<'arena, T: Send> Sync for SlabPerThreadState<'arena, T> {}

const REMOTE_FREE_FLAGS_STATE_NORMAL0: usize = 0b00;
const REMOTE_FREE_FLAGS_STATE_IN_FULL_LIST: usize = 0b01;
const _REMOTE_FREE_FLAGS_STATE_IN_DELAYED_FREE_LIST: usize = 0b11;
const REMOTE_FREE_FLAGS_STATE_NORMAL1: usize = 0b10;

impl<'arena, T: Send> SlabPerThreadState<'arena, T> {
    /// Initialize state
    pub unsafe fn init(self_: *mut Self, tid: u64, root: &'arena SlabRoot<'arena, T>) {
        // alloc initial segment
        let new_initial_seg = SlabSegmentHdr::<'arena, T>::alloc_new_seg(tid);
        let new_initial_seg = unsafe {
            // 😱 this is super dangerous wrt uninit memory
            // hopefully it doesn't break
            (*new_initial_seg).owning_thread_state = mem::transmute(self_);
            (*new_initial_seg).next = None;
            &*new_initial_seg
        };

        unsafe {
            (*self_).tid = tid;
            (*self_).root = root;
            (*self_).segments = Cell::new(new_initial_seg);
            (*self_).pages = Cell::new(&new_initial_seg.pages[0]);
            (*self_).last_page = Cell::new(&new_initial_seg.pages[PAGES_PER_SEG - 1]);
            (*self_).thread_delayed_free = AtomicPtr::new(ptr::null_mut());
        }

        // safety: we initialized everything
    }

    /// Allocate a new segment, link it into segments list,
    /// and make it the *entirety* of the pages list
    fn new_seg(&'arena self) {
        let new_seg = SlabSegmentHdr::<'arena, T>::alloc_new_seg(self.tid);
        let old_seg_head = Some(self.segments.get());
        let new_seg = unsafe {
            (*new_seg).owning_thread_state = self;
            (*new_seg).next = old_seg_head;
            // safety: at this point we've initialized everything
            // *including* the owning_thread_state footgun
            &*new_seg
        };
        self.segments.set(new_seg);
        self.pages.set(&new_seg.pages[0]);
        self.last_page.set(&new_seg.pages[PAGES_PER_SEG - 1]);
    }

    /// Allocation slow path
    ///
    /// Returns a block, which must be free and ready for use
    fn alloc_slow(
        &'arena self,
    ) -> (
        &'arena SlabSegmentPageMeta<'arena, T>,
        &'arena SlabFreeBlock<'arena>,
    ) {
        // collect thread delayed free block list and free them all
        let mut thread_delayed_free = self
            .thread_delayed_free
            .fetch_update(
                Ordering::SeqCst,
                Ordering::SeqCst,
                |_| Some(ptr::null_mut()),
            )
            .unwrap();

        while !thread_delayed_free.is_null() {
            unsafe {
                // fixme transmute eww yuck
                let next = (*thread_delayed_free).next;
                self.free(mem::transmute(thread_delayed_free));
                thread_delayed_free = mem::transmute(next);
            }
        }

        let mut page = self.pages.get();
        loop {
            page.collect_free_lists();
            if page.this_free_list.get().is_some() {
                return (page, page.this_free_list.get().unwrap());
            } else {
                // this page is full, and so has every page we've passed by so far
                match page.next_page.get() {
                    Some(next_page) => {
                        self.pages.set(next_page);
                        page = next_page;
                    }
                    None => {
                        self.new_seg();
                        return (
                            self.pages.get(),
                            self.pages.get().this_free_list.get().unwrap(),
                        );
                    }
                }
            }
        }
    }

    /// Allocates an object from this shard
    ///
    /// Does *NOT* initialize any of the resulting memory
    pub fn alloc(&'arena self) -> &'arena SlabBlock<'arena, T> {
        let fast_page = self.pages.get();
        let fast_block = fast_page.this_free_list.get();
        let (page, block) = match fast_block {
            Some(x) => (fast_page, x), // fast path
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

            // if we got here, we *know* we're no longer full
            // (regardless of how we might race the state transition
            // between in-full-list and in-thread-delayed-list)
            // so take ourselves off if necessary.
            //
            // it is not possible to race against any other arcs,
            // as they are synchronous with us on our own thread
            let prev_remote_list = seg.pages[page_i]
                .remote_free_list
                .fetch_and(!0b11, Ordering::SeqCst);
            if prev_remote_list != REMOTE_FREE_FLAGS_STATE_NORMAL0
                && prev_remote_list != REMOTE_FREE_FLAGS_STATE_NORMAL1
            {
                seg.pages[page_i].next_page.set(None);
                self.last_page.get().next_page.set(Some(&seg.pages[page_i]));
                self.last_page.set(&seg.pages[page_i]);
            }

            let obj_mut = obj as *const _ as *mut SlabBlock<'arena, T>;
            (*obj_mut).free.next = seg.pages[page_i].local_free_list.get();
            seg.pages[page_i]
                .local_free_list
                .set(Some(mem::transmute(obj)));
        } else {
            // remote free

            // when freeing from the normal state, it is not possible to miss
            // the transition into in-full-list state because this is done atomically.
            // (so either state is normal and alloc will pick up this block we just freed,
            // or else state will change to in-full-list and we will add to the thread delayed free list).

            // when freeing from the in-full-list state it *is* possible to miss
            // the transition into the in-thread-delayed-list state.
            // the consequence of this is that this block being freed will be added
            // to the thread delayed free list even though there is already another
            // block from the same page there. this is not a correctness issue,
            // it is just less optimal than ideal

            // when freeing from the in-full-list state it *is* *ALSO* possible to miss
            // the transition back into the normal state.
            // the consequence of this is that this block being freed will *once again*
            // be added to the thread delayed free list, *AND* it will *NOT*
            // immediately end up back on the normal free list.
            // HOWEVER, as the slow path is *always* taken periodically, this block
            // has a chance to get picked up again once that happens.

            // when freeing from the in-thread-delayed-list state, the state transition
            // to the normal state doesn't matter, because we are adding to the
            // same page remote free list in either case.

            let page = &seg.pages[page_i];
            let mut prev_remote_free = page.remote_free_list.load(Ordering::SeqCst);
            loop {
                let flag_bits = prev_remote_free as usize & 0b11;
                if flag_bits != REMOTE_FREE_FLAGS_STATE_IN_FULL_LIST {
                    // normal state or in-thread-delayed-list state
                    // push onto remote free list
                    let next_block_proper_addr = (prev_remote_free as usize & !0b11) as *const _;
                    let obj_mut = obj as *const _ as *mut SlabBlock<'arena, T>;
                    (*obj_mut).free.next = Some(&*next_block_proper_addr);
                    match page.remote_free_list.compare_exchange_weak(
                        prev_remote_free,
                        (obj_ptr | flag_bits) as _,
                        Ordering::SeqCst,
                        Ordering::SeqCst,
                    ) {
                        Ok(_) => break,
                        Err(x) => prev_remote_free = x,
                    }
                } else {
                    // in-full-list state
                    page.remote_free_list.fetch_or(0b10, Ordering::SeqCst);
                    // push onto thread delayed free
                    let per_thread = seg.owning_thread_state;
                    let mut prev_thread_delayed_free =
                        per_thread.thread_delayed_free.load(Ordering::SeqCst);
                    loop {
                        let obj_mut = obj as *const _ as *mut SlabBlock<'arena, T>;
                        (*obj_mut).free.next = Some(&*prev_thread_delayed_free);
                        match per_thread.thread_delayed_free.compare_exchange_weak(
                            prev_thread_delayed_free,
                            obj_ptr as _,
                            Ordering::SeqCst,
                            Ordering::SeqCst,
                        ) {
                            Ok(_) => break,
                            Err(x) => prev_thread_delayed_free = x,
                        }
                    }
                    break;
                }
            }
        }
    }
}

/// Handle to a per-thread shard of an allocator
///
/// The only way to get one of these is to go through [SlabRoot::new_thread],
/// which ensures that at most one `SlabThreadShard` exists for each
/// `SlabPerThreadState`. This means that whoever has access to this handle
/// effectively has exclusive access to the per-thread state (except fields
/// that are explicitly managed with atomics).
///
/// It is *not* allowed for a raw `&'arena SlabPerThreadState<'arena, T>`
/// to escape from this module. Allowing this can cause data races.
pub struct SlabThreadShard<'arena, T: Send>(
    &'arena SlabPerThreadState<'arena, T>,
    /// prevent this type from being `Sync`
    PhantomData<UnsafeCell<()>>,
);

impl<'arena, T: Send> Deref for SlabThreadShard<'arena, T> {
    type Target = &'arena SlabPerThreadState<'arena, T>;

    fn deref<'guard>(&'guard self) -> &'guard &'arena SlabPerThreadState<'arena, T> {
        &self.0
    }
}

impl<'arena, T: Send> Drop for SlabThreadShard<'arena, T> {
    fn drop(&mut self) {
        let root = self.0.root;
        let mask = !(1 << self.0.tid);
        // TODO: relax ordering
        root.thread_inuse.fetch_and(mask, Ordering::SeqCst);
    }
}

/// Header for each (4 M) segment
#[repr(C)]
#[derive(Debug)]
struct SlabSegmentHdr<'arena, T: Send> {
    /// Thread that created this segment and owns its "local" data
    owning_tid: u64,
    /// Per-thread data of the thread that created this
    /// (used for thread delayed free)
    owning_thread_state: &'arena SlabPerThreadState<'arena, T>,
    /// List of segments (all owned by this thread)
    next: Option<&'arena SlabSegmentHdr<'arena, T>>,
    /// Metadata for each page within the segment
    pages: [SlabSegmentPageMeta<'arena, T>; PAGES_PER_SEG],
}

impl<'arena, T: Send> SlabSegmentHdr<'arena, T> {
    pub fn alloc_new_seg(owning_tid: u64) -> *mut Self {
        unsafe {
            let seg = alloc::alloc_zeroed(SEGMENT_LAYOUT) as *mut Self;
            (*seg).owning_tid = owning_tid;

            for i in 0..PAGES_PER_SEG {
                SlabSegmentPageMeta::init_page(addr_of_mut!((*seg).pages[i]), seg, i);
                if i != PAGES_PER_SEG - 1 {
                    let next_page_meta_ptr = addr_of_mut!((*seg).pages[i + 1]);
                    // reborrowing is safe because we *never* make &mut
                    (*seg).pages[i].next_page.set(Some(&*next_page_meta_ptr));
                }
            }

            // safety: we initialized everything EXCEPT
            // owning_thread_state which remains UNINIT!
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
struct SlabSegmentPageMeta<'arena, T: Send> {
    /// Linked list of pages
    next_page: Cell<Option<&'arena SlabSegmentPageMeta<'arena, T>>>,
    /// List that we allocate from in the fast path
    this_free_list: Cell<Option<&'arena SlabFreeBlock<'arena>>>,
    /// List that we free to from the same thread
    local_free_list: Cell<Option<&'arena SlabFreeBlock<'arena>>>,
    /// List that other threads free onto
    remote_free_list: AtomicUsize,
    _p: PhantomData<T>, // FIXME what does "covariant (with drop check)" mean?
}
// safety: we carefully use atomic operations on remote_free_list,
// and everything else is owned by one specific thread
// (which is guarded by SlabRoot::thread_inuse)
unsafe impl<'arena, T: Send> Sync for SlabSegmentPageMeta<'arena, T> {}

impl<'arena, T: Send> SlabSegmentPageMeta<'arena, T> {
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
        if self.this_free_list.get().is_some() {
            // don't actually do anything if there are blocks free
            return;
        }

        let mut is_full = true;

        // collect this thread
        let mut our_free_list = self.local_free_list.take();
        if our_free_list.is_some() {
            is_full = false;
        }

        // collect other threads
        let mut prev_remote_free = self.remote_free_list.load(Ordering::SeqCst);
        loop {
            let state = prev_remote_free & 0b11;
            let ptr = prev_remote_free & !0b11;

            // state must be normal
            debug_assert!(
                state == REMOTE_FREE_FLAGS_STATE_NORMAL0
                    || state == REMOTE_FREE_FLAGS_STATE_NORMAL1
            );

            if ptr != 0 {
                is_full = false;
            }

            let remote_free_new_ptr_with_flags = if is_full {
                debug_assert!(ptr == 0);
                REMOTE_FREE_FLAGS_STATE_IN_FULL_LIST
            } else {
                REMOTE_FREE_FLAGS_STATE_NORMAL0
            };

            match self.remote_free_list.compare_exchange_weak(
                prev_remote_free,
                remote_free_new_ptr_with_flags,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => break,
                Err(x) => prev_remote_free = x,
            }
        }

        let remote_free_list_ptr = (prev_remote_free & !0b11) as *const SlabFreeBlock<'arena>;

        // the only possible state transition allowed here for the remote free list is
        // normal -> in-full-list
        // the race that needs to be checked for is "we put this page on the full list,
        // but at the same time another thread frees something (making it not full anymore)
        // but we miss that free and thus never manage to access this block again"
        //
        // this is prevented because:
        // * freeing from the in-full-list state will put something onto the thread delayed free list
        //   (i.e. we have another chance to recover this block the next time we go through the slow path)
        // * freeing from the in-thread-delayed-list state requires moving through the in-full-list state
        // * when freeing from the normal state, setting the state to in-full-list
        //   is atomic with consuming the remote free list

        if !remote_free_list_ptr.is_null() {
            // append to end of our free list
            if our_free_list.is_none() {
                // only remote free, none of ours
                self.this_free_list.set(Some(unsafe {
                    // safety: these blocks should definitely belong to our allocation
                    // assuming we didn't mess up
                    &*remote_free_list_ptr
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
                    *(next as *mut _) = Some(&*remote_free_list_ptr);
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
    pub alloced: ManuallyDrop<MaybeUninit<T>>,
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
                slab.per_thread_state.as_ptr().offset(0) as usize,
                *shard1 as *const _ as usize
            );
        }
        let shard2 = slab.new_thread();
        assert_eq!(slab.thread_inuse.load(Ordering::SeqCst), 0b11);
        unsafe {
            assert_eq!(
                slab.per_thread_state.as_ptr().offset(1) as usize,
                *shard2 as *const _ as usize
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
                slab.per_thread_state.as_ptr().offset(0) as usize,
                *shard1_2 as *const _ as usize
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
        let obj_1 = thread_shard.alloc();
        let obj_2 = thread_shard.alloc();
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        assert_eq!(obj_1 as *const _ as usize + 8, obj_2 as *const _ as usize);

        unsafe { thread_shard.free(obj_2) };
        unsafe { thread_shard.free(obj_1) };

        unsafe {
            let seg = thread_shard.segments.get();
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
        let obj_1 = thread_shard_0.alloc();
        let obj_2 = thread_shard_0.alloc();
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        let thread_shard_1 = alloc.new_thread();
        unsafe { thread_shard_1.free(obj_2) };
        unsafe { thread_shard_1.free(obj_1) };

        unsafe {
            let seg = thread_shard_0.segments.get();
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
        let obj_1 = thread_shard.alloc();
        let obj_2 = thread_shard.alloc();
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        unsafe { thread_shard.free(obj_1) };
        unsafe { thread_shard.free(obj_2) };

        let obj_1_2nd_try = thread_shard.alloc();
        let obj_2_2nd_try = thread_shard.alloc();
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
        let obj_1 = thread_shard_0.alloc();
        let obj_2 = thread_shard_0.alloc();
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        let thread_shard_1 = alloc.new_thread();
        unsafe { thread_shard_1.free(obj_1) };
        unsafe { thread_shard_1.free(obj_2) };

        let obj_1_2nd_try = thread_shard_0.alloc();
        let obj_2_2nd_try = thread_shard_0.alloc();
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
        let obj_1 = thread_shard_0.alloc();
        let obj_2 = thread_shard_0.alloc();
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        let thread_shard_1 = alloc.new_thread();
        unsafe { thread_shard_0.free(obj_1) };
        unsafe { thread_shard_1.free(obj_2) };

        let obj_1_2nd_try = thread_shard_0.alloc();
        let obj_2_2nd_try = thread_shard_0.alloc();
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

    #[test]
    fn slab_test_new_seg() {
        let alloc = SlabRoot::<[u8; 30000]>::new();
        let thread_shard = alloc.new_thread();
        let mut things = Vec::new();
        for i in 0..129 {
            let obj = thread_shard.alloc();
            println!("Allocated obj {:3} {:?}", i, obj as *const _);
            things.push(obj);
        }

        for i in 0..129 {
            let obj = things[i];
            unsafe { thread_shard.free(obj) };
            println!("Freed obj {:3}", i);
        }

        let mut things2 = Vec::new();
        for i in 0..129 {
            let obj = thread_shard.alloc();
            println!("Allocated obj {:3} again {:?}", i, obj as *const _);
            things2.push(obj);
        }

        // XXX this is a pretty unstable test
        // everything is alloc from the new segment until the 129th item
        // which comes from the existing seg, it just so happens to
        // be the second half of the first block
        assert_eq!(
            things2[128] as *const _ as usize,
            things[1] as *const _ as usize
        );
    }

    #[test]
    fn slab_test_remote_free() {
        let alloc = SlabRoot::<[u8; 30000]>::new();
        let thread_shard_0 = alloc.new_thread();
        let thread_shard_1 = alloc.new_thread();
        let mut things = Vec::new();
        for i in 0..129 {
            let obj = thread_shard_0.alloc();
            println!("Allocated obj {:3} {:?}", i, obj as *const _);
            things.push(obj);
        }

        for i in 0..129 {
            let obj = things[i];
            unsafe { thread_shard_1.free(obj) };
            println!("Freed obj {:3}", i);
        }

        // delayed free list tests
        {
            let seg1 = thread_shard_0.segments.get();
            let seg0 = seg1.next.unwrap();

            for page_i in 0..64 {
                let remote_free_list = seg0.pages[page_i].remote_free_list.load(Ordering::SeqCst);

                // each one of these should contain one block here and one block on the thread delayed free list
                assert!(remote_free_list & 0b11 == _REMOTE_FREE_FLAGS_STATE_IN_DELAYED_FREE_LIST);

                assert_eq!(
                    remote_free_list & !0b11,
                    things[page_i * 2 + 1] as *const _ as usize
                );
                unsafe {
                    assert_eq!(*((remote_free_list & !0b11) as *const usize), 0);
                }
            }
            let remote_free_list_seg1_pg0 = seg1.pages[0].remote_free_list.load(Ordering::SeqCst);
            assert!(remote_free_list_seg1_pg0 & 0b11 == REMOTE_FREE_FLAGS_STATE_NORMAL0);
            assert_eq!(
                remote_free_list_seg1_pg0 & !0b11,
                things[128] as *const _ as usize
            );
        }

        let mut test_thread_delayed_item =
            thread_shard_0.thread_delayed_free.load(Ordering::SeqCst) as *const usize;
        for i in (0..64).rev() {
            assert_eq!(
                test_thread_delayed_item as usize,
                things[i * 2] as *const _ as usize
            );
            unsafe {
                test_thread_delayed_item = *test_thread_delayed_item as *const usize;
            }
        }

        let mut things2: Vec<&SlabBlock<'_, [u8; 30000]>> = Vec::new();
        for i in 0..256 {
            let obj = thread_shard_0.alloc();
            println!("Allocated obj {:3} again {:?}", i, obj as *const _);
            things2.push(obj);
        }

        // XXX this is a pretty unstable test
        // everything is alloc from the new segment until the 129th item
        // which comes from the existing seg in this pattern
        for i in 0..128 {
            assert_eq!(
                things2[128 + i] as *const _ as usize,
                things[127 - (i ^ 1)] as *const _ as usize
            );
        }
    }
}
