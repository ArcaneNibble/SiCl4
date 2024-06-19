//! Custom slab-based memory allocator
//!
//! This is a custom concurrent slab memory allocator inspired by the
//! [sharded_slab](https://docs.rs/sharded-slab/latest/sharded_slab/implementation/index.html)
//! crate, which is in turn inspired by the
//! [Mimalloc](https://www.microsoft.com/en-us/research/uploads/prod/2019/06/mimalloc-tr-v1.pdf)
//! allocator from Microsoft Research.
//!
//! The implementation is much closer to the original Microsoft implementation than the Rust crate.
//!
//! This code has tighter integration between memory allocation and object locking.
//! Some notes as to why have been written
//! [here](https://arcanenibble.github.io/parallel-capable-netlist-data-structures-part-2.html)

use std::{
    alloc::{self, Layout},
    borrow::{Borrow, BorrowMut},
    cell::{Cell, UnsafeCell},
    cmp,
    collections::HashSet,
    fmt::Debug,
    marker::PhantomData,
    mem::{self, offset_of, size_of, MaybeUninit},
    ops::Deref,
    ptr::{self, addr_of, addr_of_mut},
    sync::atomic::Ordering,
};

use tracing::Level;

use crate::{
    loom_testing::*,
    util::{roundto, UsizePtr},
};

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

/// Workaround for inadequate const generics
///
/// Holds all of the other random functions we might need
pub trait ConstGenericsHackWorkaround<T>: BorrowMut<[T]> {
    fn init(x: T) -> Self
    where
        T: Copy;

    fn as_mut_ptr(self_: *mut Self) -> *mut T;
}
impl<T, const N: usize> ConstGenericsHackWorkaround<T> for [T; N] {
    #[inline]
    fn init(x: T) -> Self
    where
        T: Copy,
    {
        [x; N]
    }

    #[inline]
    fn as_mut_ptr(self_: *mut Self) -> *mut T {
        // safety: assume that it doesn't matter if metadata is invalid for a slice pointer
        unsafe { addr_of_mut!((*self_)[0]) }
    }
}

/// Trait that maps (types which can be allocated) -> (allocator bin index)
///
/// Mapping multiple types to the same bin is allowed,
/// but each bin will be sized to contain the *largest* item
///
/// Example:
///
/// ```
/// use core::alloc::Layout;
/// use sicl4_db::allocator::{TypeMapper, TypeMappable};
///
/// struct ExampleMapper {}
/// impl TypeMapper for ExampleMapper {
///     type BinsArrayTy<T> = [T; 2];
///     const LAYOUTS: &'static [&'static [Layout]] = &[
///         &[Layout::new::<u8>()],
///         &[Layout::new::<u16>(), Layout::new::<u32>()],
///     ];
/// }
/// impl TypeMappable<ExampleMapper> for u8 {
///     const I: usize = 0;
/// }
/// impl TypeMappable<ExampleMapper> for u16 {
///     const I: usize = 1;
/// }
/// impl TypeMappable<ExampleMapper> for u32 {
///     const I: usize = 1;
/// }
/// ```
pub trait TypeMapper {
    /// GAT array with size equal to the number of allocator bins
    /// (i.e. this many unique types)
    ///
    /// GAT is needed to work around limitations of const generics
    type BinsArrayTy<T>: ConstGenericsHackWorkaround<T>;

    /// Layouts contained in each bin
    const LAYOUTS: &'static [&'static [Layout]];

    fn type_to_bin<T: TypeMappable<Self>>() -> usize
    where
        Self: Sized,
    {
        T::I
    }
}
/// Trait that maps (type which can be allocated) -> (allocator bin index)
///
/// Also helps ensure that allocator only stores `Send + Sync` items
pub trait TypeMappable<M>: Send + Sync {
    const I: usize;
}

/// Slab allocator root object
pub struct SlabRoot<'arena, Mapper: TypeMapper> {
    /// Bitfield, where a `1` bit in position `n` indicates that
    /// a [SlabThreadShard] has been handed out for the nth entry of
    /// [per_thread_state](Self::per_thread_state)
    /// (and it hasn't been dropped yet)
    thread_inuse: AtomicU64,
    /// Actual storage for per-thread data
    per_thread_state: [UnsafeCell<MaybeUninit<SlabPerThreadState<'arena, Mapper>>>; MAX_THREADS],
    /// Indicates whether or not the state has been initialized
    per_thread_state_inited: [Cell<bool>; MAX_THREADS],
    /// Ensure `'arena` lifetime is invariant
    _p: PhantomData<Cell<&'arena ()>>,
}
// safety: nothing requires that we stay on the same thread
// (the borrow of 'arena takes care of pinning as necessary)
unsafe impl<'arena, Mapper: TypeMapper> Send for SlabRoot<'arena, Mapper> {}
// safety: we carefully use atomic operations on thread_inuse
unsafe impl<'arena, Mapper: TypeMapper> Sync for SlabRoot<'arena, Mapper> {}

impl<'arena, Mapper: TypeMapper> Debug for SlabRoot<'arena, Mapper> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // xxx getting the locking correct here seems tricky so just give up and don't bother
        f.debug_struct("SlabRoot")
            .field("@addr", &(self as *const _))
            .field("thread_inuse", &self.thread_inuse.load(Ordering::Relaxed))
            .finish()
    }
}

impl<'arena, Mapper: TypeMapper> SlabRoot<'arena, Mapper> {
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
    /// Panics if [MAX_THREADS] is reached, or if a global lock exists
    pub fn new_thread(&'arena self) -> SlabThreadShard<'arena, Mapper> {
        let allocated_tid;
        // order: need to synchronize-with only the thread that set
        // thread_inuse such that it allows us to (re)allocate a particular thread id
        // release operations by other threads in the meantime do not matter
        // (as they do not allow reallocating the relevant thread id)
        // successful new_thread calls by other threads in the meantime
        // will form part of the release sequence
        let mut old_inuse = self.thread_inuse.load(Ordering::Relaxed);
        loop {
            let next_tid = old_inuse.trailing_ones();
            if next_tid as usize >= MAX_THREADS {
                panic!("No more threads allowed, or global lock acquired!");
            }
            let new_inuse = old_inuse | (1 << next_tid);
            match self.thread_inuse.compare_exchange_weak(
                old_inuse,
                new_inuse,
                Ordering::Acquire,
                Ordering::Relaxed,
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
            let per_thread_maybe_uninit = &mut *self.per_thread_state[allocated_tid].get();
            if !self.per_thread_state_inited[allocated_tid].get() {
                SlabPerThreadState::<'arena, Mapper>::init(
                    per_thread_maybe_uninit.as_mut_ptr(),
                    allocated_tid as u64,
                );
                self.per_thread_state_inited[allocated_tid].set(true);
            }
            per_thread_maybe_uninit.assume_init_ref()
        };
        SlabThreadShard(thread_state, PhantomData)
    }

    /// Try and get a handle for performing global operations
    pub fn try_lock_global(&'arena self) -> Option<SlabRootGlobalGuard<'arena, Mapper>> {
        // order: need to synchronize-with only the thread that set
        // thread_inuse to 0, after which we will read/write fresh updated data
        match self
            .thread_inuse
            .compare_exchange(0, u64::MAX, Ordering::Acquire, Ordering::Relaxed)
        {
            Ok(_) => Some(SlabRootGlobalGuard(self, PhantomData)),
            Err(_) => None,
        }
    }
}

/// Handle for performing global operations on the heap
///
/// The only way to get one of these is to go through [SlabRoot::try_lock_global]
/// All the dangerous operations are only implemented on this object.
pub struct SlabRootGlobalGuard<'arena, Mapper: TypeMapper>(
    &'arena SlabRoot<'arena, Mapper>,
    /// prevent this type from being `Sync`
    PhantomData<UnsafeCell<()>>,
);

impl<'arena, Mapper: TypeMapper> Debug for SlabRootGlobalGuard<'arena, Mapper> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // because we gave up on getting debug correct in SlabRoot,
        // reach inside and do all the relevant debug printing here instead
        let mut fields = f.debug_struct(&format!("SlabRootGlobalGuard(@{:?})", self.0 as *const _));
        for i in 0..MAX_THREADS {
            if !self.0.per_thread_state_inited[i].get() {
                fields.field(&format!("per_thread_state[{}]", i), &"<uninit>");
            } else {
                fields.field(&format!("per_thread_state[{}]", i), unsafe {
                    (&*self.0.per_thread_state[i].get()).assume_init_ref()
                });
            }
        }
        fields.finish()
    }
}

impl<'arena, Mapper: TypeMapper> Drop for SlabRootGlobalGuard<'arena, Mapper> {
    fn drop(&mut self) {
        let root = self.0;
        // ordering: need all manipulation of thread-owned data to stick
        root.thread_inuse.store(0, Ordering::Release);
    }
}

impl<'guard, 'arena, Mapper: TypeMapper> SlabRootGlobalGuard<'arena, Mapper> {
    fn __debug_check_ty_missing_blocks(
        thread_i: usize,
        per_thread_per_ty: &'arena SlabPerThreadPerTyState<'arena>,
    ) -> HashSet<usize> {
        let mut all_outstanding_blocks = HashSet::new();
        println!("Checking state for thread {}", thread_i);

        let mut thread_delayed_free_blocks = HashSet::new();
        let delayed_free_block = per_thread_per_ty
            .thread_delayed_free
            .load(Ordering::Relaxed);

        let mut delayed_free_block = unsafe { delayed_free_block.as_ref() };
        while let Some(delayed_free_block_inner) = delayed_free_block {
            println!("thread delayed free: {:?}", delayed_free_block_inner);
            thread_delayed_free_blocks.insert(delayed_free_block_inner as *const _ as usize);
            delayed_free_block = delayed_free_block_inner.load_next();
        }

        let mut page_linked_list_set = HashSet::new();
        let mut avail_page = per_thread_per_ty.pages.get();
        loop {
            println!("Page on linked list: {:?}", avail_page as *const _);
            page_linked_list_set.insert(avail_page as *const _ as usize);

            if avail_page.next_page.get().is_some() {
                avail_page = avail_page.next_page.get().unwrap();
            } else {
                let last_page = per_thread_per_ty.last_page.get();
                assert_eq!(avail_page as *const _, last_page);
                break;
            }
        }

        let mut seg = per_thread_per_ty.segments.get();
        loop {
            println!("Checking segment {:?}", seg as *const _);

            for page_i in 0..PAGES_PER_SEG {
                let page = &seg.pages[page_i];
                println!("Checking page {} {:?}", page_i, page);

                let num_objects = SlabSegmentHdr::get_num_objects(seg, page_i == 0);
                let mut outstanding_blocks = HashSet::new();

                for obj_i in 0..num_objects {
                    let obj_ptr = SlabSegmentHdr::get_addr_of_block(seg, page_i, obj_i);
                    outstanding_blocks.insert(obj_ptr as usize);
                }

                let mut this_free = page.this_free_list.get();
                while let Some(this_free_block) = this_free {
                    println!("This free list item: {:?}", this_free_block as *const _);
                    let was_outstanding =
                        outstanding_blocks.remove(&(this_free_block as *const _ as usize));

                    if !was_outstanding {
                        panic!("Block not in page or found in multiple free lists!");
                    }

                    this_free = this_free_block.load_next();
                }

                let mut local_free = page.local_free_list.get();
                while let Some(this_free_block) = local_free {
                    println!("Local free list item: {:?}", this_free_block as *const _);
                    let was_outstanding =
                        outstanding_blocks.remove(&(this_free_block as *const _ as usize));

                    if !was_outstanding {
                        panic!("Block not in page or found in multiple free lists!");
                    }

                    local_free = this_free_block.load_next();
                }

                let remote_free = page.remote_free_list.load(Ordering::Relaxed);
                let mut remote_free_ptr = unsafe {
                    let ptr = (remote_free & !0b11) as *const SlabFreeBlock;
                    ptr.as_ref()
                };
                let remote_free_flags = remote_free & 0b11;
                while let Some(this_free_block) = remote_free_ptr {
                    println!("Remote free list item: {:?}", this_free_block as *const _);
                    let was_outstanding =
                        outstanding_blocks.remove(&(this_free_block as *const _ as usize));

                    if !was_outstanding {
                        panic!("Block not in page or found in multiple free lists!");
                    }

                    remote_free_ptr = this_free_block.load_next();
                }

                let full_without_thread_delayed_free = outstanding_blocks.len() == num_objects;

                let mut delayed_free_block_for_this_page = None;
                for x in &thread_delayed_free_blocks {
                    let was_removed = outstanding_blocks.remove(x);
                    if was_removed {
                        if delayed_free_block_for_this_page.is_some() {
                            panic!("ERR: page in thread delayed free multiple times");
                        }
                        delayed_free_block_for_this_page = Some(*x);
                    }
                }
                if let Some(x) = delayed_free_block_for_this_page {
                    thread_delayed_free_blocks.remove(&x);
                }
                let was_in_thread_delayed_blocks = delayed_free_block_for_this_page.is_some();

                println!("The following blocks are still allocated:");
                for x in &outstanding_blocks {
                    println!("* 0x{:x}", x);
                    all_outstanding_blocks.insert(*x);
                }

                let full_actually_full = outstanding_blocks.len() == num_objects;

                if remote_free_flags == REMOTE_FREE_FLAGS_STATE_NORMAL {
                    // If the page is normal, it must be in the list
                    assert!(page_linked_list_set.contains(&(page as *const _ as usize)));
                    // it may be full if it's the very first page (i.e. we haven't noticed yet)
                    if per_thread_per_ty.pages.get() as *const _ != page {
                        // it cannot require thread delayed free to become unfull
                        assert!(!full_without_thread_delayed_free);
                    }
                } else if remote_free_flags == REMOTE_FREE_FLAGS_STATE_IN_FULL_LIST {
                    // If the page is in-full-list it cannot be linked
                    assert!(!page_linked_list_set.contains(&(page as *const _ as usize)));
                    // it must be *full* full
                    assert!(full_actually_full);
                    // it *cannot* exist in thread delayed blocks yet
                    assert!(!was_in_thread_delayed_blocks);
                } else if remote_free_flags == REMOTE_FREE_FLAGS_STATE_IN_DELAYED_FREE_LIST {
                    // If the page is in-thread-delayed-list it cannot be linked
                    assert!(!page_linked_list_set.contains(&(page as *const _ as usize)));
                    // it *must* exist in thread delayed blocks
                    assert!(was_in_thread_delayed_blocks);
                    // at this point (stable, no threads running)
                    // it cannot have any local free blocks
                    assert!(page.this_free_list.get().is_none());
                    assert!(page.local_free_list.get().is_none());
                } else {
                    panic!("Illegal remote free state encountered");
                }
            }

            if seg.next.is_some() {
                seg = seg.next.unwrap();
            } else {
                break;
            }
        }

        if thread_delayed_free_blocks.len() > 0 {
            println!("BAD! thread delayed free blocks exist that don't belong to us!");
            for x in &thread_delayed_free_blocks {
                println!("* 0x{:x}", x);
            }
            panic!();
        }

        all_outstanding_blocks
    }

    // returns outstanding blocks for cells and wires in separate hashsets
    pub fn _debug_check_missing_blocks(&'guard self) -> Vec<HashSet<usize>> {
        let mut all_outstanding_blocks = Vec::new();
        let num_tys = Mapper::BinsArrayTy::<()>::init(()).borrow().len();
        for _ in 0..num_tys {
            all_outstanding_blocks.push(HashSet::new());
        }

        for thread_i in 0..MAX_THREADS {
            if self.0.per_thread_state_inited[thread_i].get() {
                let per_thread =
                    unsafe { (&*self.0.per_thread_state[thread_i].get()).assume_init_ref() };
                let per_tys = per_thread.per_ty_state.borrow();
                for type_bin_i in 0..num_tys {
                    println!("~~~~~ Checking type bin {} ~~~~~", type_bin_i);
                    let outstanding_cells_this_thread =
                        Self::__debug_check_ty_missing_blocks(thread_i, &per_tys[type_bin_i]);
                    for x in outstanding_cells_this_thread {
                        all_outstanding_blocks[type_bin_i].insert(x);
                    }
                }
            }
        }
        all_outstanding_blocks
    }
}

/// Slab allocator per-thread state (actual contents)
pub struct SlabPerThreadState<'arena, Mapper: TypeMapper> {
    /// Identifies this thread
    ///
    /// Current impl: bit position in the [SlabRoot::thread_inuse] bitfield
    pub(crate) tid: u64,
    /// Manages the memory for each type
    per_ty_state: Mapper::BinsArrayTy<SlabPerThreadPerTyState<'arena>>,
    /// ABA generation counter for each type
    generation: Mapper::BinsArrayTy<Cell<u64>>,
}
// safety: only one thread can have a SlabThreadShard to access any fields here
unsafe impl<'arena, Mapper: TypeMapper> Sync for SlabPerThreadState<'arena, Mapper> {}

impl<'arena, Mapper: TypeMapper> Debug for SlabPerThreadState<'arena, Mapper> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SlabPerThreadState")
            .field("@addr", &(self as *const _))
            .field("tid", &self.tid)
            .field("per_ty_state", &self.per_ty_state.borrow())
            .field("generation", &self.generation.borrow())
            .finish()
    }
}

impl<'arena, Mapper: TypeMapper> SlabPerThreadState<'arena, Mapper> {
    /// Initialize state
    pub unsafe fn init(self_: *mut Self, tid: u64) {
        // calculate layouts
        let mut layouts = Mapper::BinsArrayTy::<(usize, usize)>::init((0, 0));
        let layouts = layouts.borrow_mut();
        for type_bin_i in 0..layouts.len() {
            let mut sz = Layout::new::<SlabFreeBlock>().size();
            let mut align = Layout::new::<SlabFreeBlock>().align();

            for layout in Mapper::LAYOUTS[type_bin_i] {
                sz = cmp::max(sz, layout.size());
                align = cmp::max(align, layout.align());
            }

            sz = roundto(sz, align);

            layouts[type_bin_i] = (sz, align);
        }

        let ty_states = Mapper::BinsArrayTy::<SlabPerThreadPerTyState<'arena>>::as_mut_ptr(
            addr_of_mut!((*self_).per_ty_state),
        );
        for type_bin_i in 0..layouts.len() {
            let layout_i =
                Layout::from_size_align(layouts[type_bin_i].0, layouts[type_bin_i].1).unwrap();
            SlabPerThreadPerTyState::init(ty_states.add(type_bin_i), tid, layout_i);
        }

        (*self_).tid = tid;

        let generations =
            Mapper::BinsArrayTy::<Cell<u64>>::as_mut_ptr(addr_of_mut!((*self_).generation));
        for type_bin_i in 0..layouts.len() {
            (*generations.add(type_bin_i)) = Cell::new(0);
        }

        // safety: we initialized everything
    }

    /// Allocate an object from this shard
    ///
    /// Does *NOT* initialize any of the resulting memory
    pub fn allocate<T: TypeMappable<Mapper>>(&'arena self) -> (&'arena mut MaybeUninit<T>, u64) {
        let trace_span = tracing::span!(
            Level::TRACE,
            "allocator::allocate",
            tid = self.tid,
            "type" = std::any::type_name::<T>()
        );
        let _span_enter = trace_span.enter();

        let type_bin = Mapper::type_to_bin::<T>();
        let ty_state = &self.per_ty_state.borrow()[type_bin];
        let gen_ent = &self.generation.borrow()[type_bin];

        let cur_gen = gen_ent.get();
        gen_ent.set(cur_gen + 1);
        let allocated_ptr = ty_state.alloc(self.tid);
        tracing::event!(
            Level::TRACE,
            type_bin,
            ptr = ?UsizePtr::from(allocated_ptr),
            gen = cur_gen
        );
        // safety: when object leaves us, it's big enough and aligned enough for a T
        // we don't try to use it as a SlabFreeBlock until it comes back
        (unsafe { mem::transmute(allocated_ptr) }, cur_gen)
    }

    /// Deallocates an object from this shard
    ///
    /// Object must be part of this slab, not already be freed,
    /// and no other references may exist after calling free
    pub unsafe fn free<T: TypeMappable<Mapper>>(&'arena self, obj: &'arena T) {
        let trace_span = tracing::span!(
            Level::TRACE,
            "allocator::free",
            tid = self.tid,
            "type" = std::any::type_name::<T>()
        );
        let _span_enter = trace_span.enter();
        tracing::event!(Level::TRACE, ptr = ?UsizePtr::from(obj));

        let type_bin = Mapper::type_to_bin::<T>();
        let ty_state = &self.per_ty_state.borrow()[type_bin];

        ty_state.free(self.tid, obj as *const T as *mut ());
    }
}

/// Slab allocator per-thread *and* per-type state
struct SlabPerThreadPerTyState<'arena> {
    /// The layout to use when allocating
    layout: Layout,
    /// Pointer to segment list (used for global ops) TODO
    segments: Cell<&'arena SlabSegmentHdr<'arena>>,
    /// Pointer to head of (non-full) page list
    pages: Cell<&'arena SlabSegmentPageMeta<'arena>>,
    /// Pointer to end of (non-full) page list
    last_page: Cell<&'arena SlabSegmentPageMeta<'arena>>,
    /// List of blocks freed by another thread when the containing page was full
    ///
    /// This is an optimization to prevent having to search through many full pages
    thread_delayed_free: AtomicPtr<SlabFreeBlock<'arena>>,
}

impl<'arena> Debug for SlabPerThreadPerTyState<'arena> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SlabPerThreadPerTyState")
            .field("@addr", &(self as *const _))
            .field("layout", &self.layout)
            .field("segments", &(self.segments.get() as *const _))
            .field("pages", &(self.pages.get() as *const _))
            .field("last_page", &(self.last_page.get() as *const _))
            .field(
                "thread_delayed_free",
                &(self.thread_delayed_free.load(Ordering::Relaxed)),
            )
            .finish()
    }
}

/// Flags shoved into low bits of [SlabSegmentPageMeta::remote_free_list]
///
/// This state is "normal" and indicates that the page is not full
/// (and is thus part of the owning thread's page linked list).
const REMOTE_FREE_FLAGS_STATE_NORMAL: usize = 0b00;
/// Flags shoved into low bits of [SlabSegmentPageMeta::remote_free_list]
///
/// This state is "in-full-list" and indicates that the page is full
/// (and is thus no longer part of the owning thread's page linked list).
/// If something is remote freed in this page, that block needs to end
/// up on the thread delayed free block list.
const REMOTE_FREE_FLAGS_STATE_IN_FULL_LIST: usize = 0b01;
/// Flags shoved into low bits of [SlabSegmentPageMeta::remote_free_list]
///
/// This state is "in-thread-delayed-list" and indicates that the page is full
/// (and is thus no longer part of the owning thread's page linked list).
/// Additionally, it means that something has already been remote freed
/// inside this page (that previous something is on the
/// thread delayed free block list of the thread that owns this page).
/// As an optimization, remote freeing can once again happen onto the
/// page-local remote free list, because that *previous* something is
/// sufficient to bring the page back into the linked list where
/// the rest of the page-local remote free list will be swept eventually.
const REMOTE_FREE_FLAGS_STATE_IN_DELAYED_FREE_LIST: usize = 0b11;
/// Flags shoved into low bits of [SlabSegmentPageMeta::remote_free_list]
///
/// This bit pattern is invalid
const _REMOTE_FREE_FLAGS_STATE_INVALID: usize = 0b10;

impl<'arena> SlabPerThreadPerTyState<'arena> {
    /// Initialize state
    pub unsafe fn init(self_: *mut Self, tid: u64, layout: Layout) {
        // this is needed at the very beginning
        // because init_new_seg requires it
        (*self_).layout = layout;

        // alloc initial segment
        let new_initial_seg = alloc::alloc_zeroed(SEGMENT_LAYOUT) as *mut SlabSegmentHdr<'arena>;
        let new_initial_seg = unsafe {
            // 😱 this is super dangerous wrt uninit memory
            // hopefully it doesn't break
            (*new_initial_seg).owning_thread_ty_state = mem::transmute(self_);
            (*new_initial_seg).next = None;
            SlabSegmentHdr::init_new_seg(new_initial_seg, tid);
            // safety: at this point we've initialized everything
            // *including* the owning_thread_ty_state footgun
            &*new_initial_seg
        };

        (*self_).segments = Cell::new(new_initial_seg);
        (*self_).pages = Cell::new(&new_initial_seg.pages[0]);
        (*self_).last_page = Cell::new(&new_initial_seg.pages[PAGES_PER_SEG - 1]);
        (*self_).thread_delayed_free = AtomicPtr::new(ptr::null_mut());

        // safety: we initialized everything
    }

    /// Allocate a new segment, link it into segments list,
    /// and make it the *entirety* of the pages list
    ///
    /// Memory unsafety is contained, but this can mess up invariants
    /// (and thus isn't public)
    fn new_seg(&'arena self, tid: u64) {
        let trace_span = tracing::span!(Level::TRACE, "allocator::per_thread_per_ty::new_seg");
        let _span_enter = trace_span.enter();

        let new_seg = unsafe { alloc::alloc_zeroed(SEGMENT_LAYOUT) as *mut SlabSegmentHdr<'arena> };
        let old_seg_head = Some(self.segments.get());
        let new_seg = unsafe {
            (*new_seg).owning_thread_ty_state = self;
            (*new_seg).next = old_seg_head;
            SlabSegmentHdr::init_new_seg(new_seg, tid);
            // safety: at this point we've initialized everything
            // *including* the owning_thread_ty_state footgun
            &*new_seg
        };
        self.segments.set(new_seg);
        self.pages.set(&new_seg.pages[0]);
        self.last_page.set(&new_seg.pages[PAGES_PER_SEG - 1]);

        tracing::event!(Level::TRACE, ptr = ?UsizePtr::from(new_seg));
    }

    /// Allocation slow path
    ///
    /// Returns a block, which must be free and ready for use
    fn alloc_slow(
        &'arena self,
        tid: u64,
    ) -> (
        &'arena SlabSegmentPageMeta<'arena>,
        &'arena SlabFreeBlock<'arena>,
    ) {
        // collect thread delayed free block list and free them all
        // order: on success, we need to see *all* of the writes to the next pointers
        // that have been set by other threads remote freeing, so order is acquire
        // this will obviously synchronize-with the most recent write.
        // as for previous writes, the intermediate updates to thread_delayed_free
        // are RmW operations, so they will be part of the release sequence of
        // the previous (now overwritten) writes to thread_delayed_free.
        // thus this will synchronize-with *all* of those
        let thread_delayed_free = self
            .thread_delayed_free
            .fetch_update(Ordering::Acquire, Ordering::Relaxed, |_| {
                Some(ptr::null_mut())
            })
            .unwrap();

        unsafe {
            // safety: these blocks should definitely belong to our allocation
            // assuming we didn't mess up
            let mut thread_delayed_free = thread_delayed_free.as_ref();
            while let Some(block) = thread_delayed_free {
                let next = block.load_next();
                self.free(tid, block as *const _ as *mut ());
                thread_delayed_free = next;
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
                        // here we actually unlink the full page we just passed
                        // the remote free list flag update happens inside
                        // collect_free_lists (where correctness is more carefully explained)
                        self.pages.set(next_page);
                        page = next_page;
                    }
                    None => {
                        // here we have run out of memory in our heap and need to ask the OS for more
                        self.new_seg(tid);
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
    pub fn alloc(&'arena self, tid: u64) -> *mut () {
        let fast_page = self.pages.get();
        let fast_block = fast_page.this_free_list.get();
        let (page, block) = match fast_block {
            Some(x) => (fast_page, x), // fast path
            None => self.alloc_slow(tid),
        };
        page.this_free_list.set(block.load_next());
        block as *const _ as *mut ()
    }

    /// Deallocates an object
    ///
    /// Object must be part of this slab, not already be freed,
    /// and no other references may exist after calling free
    pub unsafe fn free(&'arena self, tid: u64, obj: *mut ()) {
        // sigh
        #[cfg(loom)]
        unsafe {
            (*(obj as *mut SlabFreeBlock)).next = AtomicU64::new(0);
        }

        let obj_ptr = obj as usize;
        let seg_ptr = obj_ptr & !(SEGMENT_SZ - 1);
        let seg = &*(seg_ptr as *const SlabSegmentHdr<'arena>);
        let page_i = (obj_ptr - seg_ptr) >> ALLOC_PAGE_SHIFT;
        let obj = &*(obj as *const SlabFreeBlock);

        // we don't allow freeing null so unlike msft we don't need to check for it

        if tid == (*seg).owning_tid {
            // local free (incl. thread delayed free)

            // if we got here, we *know* we're no longer full
            // (regardless of how we might race the state transition
            // between in-full-list and in-thread-delayed-list)
            // so take ourselves off of the full list if necessary
            // (i.e. link this page back in).
            //
            // it is not possible to race against any other arcs,
            // as they are synchronous with us on our own thread
            //
            // order: at this point, we don't (yet) care about any of the
            // data that other threads might've written to memory that
            // might've made its way over to us. only the state itself matters.
            // (this *will* matter in collect_free_lists, but not here)
            let prev_remote_list = seg.pages[page_i]
                .remote_free_list
                .fetch_and(!0b11, Ordering::Relaxed);
            let prev_remote_list_flags = prev_remote_list & 0b11;
            debug_assert!(prev_remote_list_flags != _REMOTE_FREE_FLAGS_STATE_INVALID);
            if prev_remote_list_flags != REMOTE_FREE_FLAGS_STATE_NORMAL {
                seg.pages[page_i].next_page.set(None);
                self.last_page.get().next_page.set(Some(&seg.pages[page_i]));
                self.last_page.set(&seg.pages[page_i]);
            }

            obj.store_next(seg.pages[page_i].local_free_list.get());
            seg.pages[page_i].local_free_list.set(Some(obj));
        } else {
            // remote free

            // when in the normal state, the only valid state transition is
            // into the in-full-list state, performed in the allocation path.
            // we cannot miss that because it is done atomically,
            // so either state is normal and collect_free_lists in the allocation path
            // will pick up this block we just freed, or else state will change to
            // in-full-list and we will add to the thread delayed free list.

            // when in the in-full-list state, the only valid state transitions
            // are into normal and into in-thread-delayed-list
            // (racing against a local free in the thread that owns the page
            // vs racing against yet another thread remote freeing into the same page as us).
            //
            // in the former case, if the remote change to the normal state happens first,
            // then we notice and end up on the page remote free list.
            // the page is removed from the full list by the owning thread doing the local free,
            // and the page remote free list will get swept eventually.
            // if our change to in-thread-delayed-list happens first, then
            // we end up on the thread delayed block list. the state still ends up
            // being unconditionally set back to normal, and the owning thread
            // still removes the page from the full list. eventually the thread
            // delayed block list will get swept and this block freed properly.
            //
            // in the latter case, one and only one of the threads will win
            // the transition into in-thread-delayed-list. that one thread
            // ends up putting the block onto the thread delayed block list.
            // it does not matter which one.
            //
            // this location is the only place where the
            // in-full-list -> in-thread-delayed-list state transition can occur

            // when in the in-thread-delayed-list state, the only possible
            // state transition to race against is into normal.
            // this state transition does not affect us as we are adding to the
            // same page remote free list in either case.

            let page = &seg.pages[page_i];
            let mut prev_remote_free = page.remote_free_list.load(Ordering::Relaxed);
            loop {
                let flag_bits = prev_remote_free & 0b11;
                if flag_bits == REMOTE_FREE_FLAGS_STATE_IN_FULL_LIST {
                    // in-full-list state
                    // try to transition into in-thread-delayed-list state

                    let new_remote_free =
                        (prev_remote_free & !0b11) | REMOTE_FREE_FLAGS_STATE_IN_DELAYED_FREE_LIST;

                    // order: here we are only making an atomic state transition,
                    // and we haven't written any memory that needs to be exposed
                    // (we only do that if we *succeed* at the state transition)
                    // so order is relaxed
                    match page.remote_free_list.compare_exchange_weak(
                        prev_remote_free,
                        new_remote_free,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => {
                            // we won, so push onto thread delayed free
                            let per_thread_per_ty = seg.owning_thread_ty_state;
                            let mut prev_thread_delayed_free = per_thread_per_ty
                                .thread_delayed_free
                                .load(Ordering::Relaxed);
                            loop {
                                obj.store_next(prev_thread_delayed_free.as_ref());
                                // order: on success, we are currently the most recent
                                // modification to thread_delayed_free
                                // we use release ordering so that writes to obj.free.next
                                // happens-before processing of it in the allocation slow path
                                match per_thread_per_ty.thread_delayed_free.compare_exchange_weak(
                                    prev_thread_delayed_free,
                                    obj_ptr as _,
                                    Ordering::Release,
                                    Ordering::Relaxed,
                                ) {
                                    Ok(_) => break,
                                    Err(x) => prev_thread_delayed_free = x,
                                }
                            }
                            break;
                        }
                        Err(x) => prev_remote_free = x,
                    }
                } else if flag_bits == REMOTE_FREE_FLAGS_STATE_NORMAL
                    || flag_bits == REMOTE_FREE_FLAGS_STATE_IN_DELAYED_FREE_LIST
                {
                    // normal state or in-thread-delayed-list state
                    // push onto remote free list
                    let next_block_proper_addr =
                        (prev_remote_free & !0b11) as *const SlabFreeBlock<'arena>;
                    obj.store_next(next_block_proper_addr.as_ref());
                    // order: on success, we are currently the most recent
                    // modification to remote_free_list
                    // we use release ordering so that writes to obj.free.next
                    // happens-before processing of it in the allocation slow path
                    match page.remote_free_list.compare_exchange_weak(
                        prev_remote_free,
                        obj_ptr | flag_bits,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => break,
                        Err(x) => prev_remote_free = x,
                    }
                } else {
                    panic!("Illegal remote free state encountered");
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
pub struct SlabThreadShard<'arena, Mapper: TypeMapper>(
    &'arena SlabPerThreadState<'arena, Mapper>,
    /// prevent this type from being `Sync`
    PhantomData<UnsafeCell<()>>,
);

impl<'arena, Mapper: TypeMapper> Debug for SlabThreadShard<'arena, Mapper> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SlabThreadShard").field(&self.0).finish()
    }
}

impl<'arena, Mapper: TypeMapper> Deref for SlabThreadShard<'arena, Mapper> {
    type Target = &'arena SlabPerThreadState<'arena, Mapper>;

    fn deref<'guard>(&'guard self) -> &'guard &'arena SlabPerThreadState<'arena, Mapper> {
        &self.0
    }
}

impl<'arena, Mapper: TypeMapper> Drop for SlabThreadShard<'arena, Mapper> {
    fn drop(&mut self) {
        let per_thread_state_offs = offset_of!(SlabRoot<Mapper>, per_thread_state);
        let my_offs =
            per_thread_state_offs + (self.tid as usize) * size_of::<SlabPerThreadState<Mapper>>();
        let my_ptr = self.0 as *const SlabPerThreadState<Mapper> as usize;
        let root_ptr = my_ptr - my_offs;
        let root = unsafe { &*(root_ptr as *const SlabRoot<Mapper>) };
        let mask = !(1 << self.0.tid);
        // ordering: need all manipulation of thread-owned data to stick
        root.thread_inuse.fetch_and(mask, Ordering::Release);
    }
}

/// Header for each (4 M) segment
#[repr(C)]
struct SlabSegmentHdr<'arena> {
    /// Thread that created this segment and owns its "local" data
    owning_tid: u64,
    /// Per-thread per-type data of the thread that created this
    /// (used for thread delayed free)
    owning_thread_ty_state: &'arena SlabPerThreadPerTyState<'arena>,
    /// List of segments (all owned by this thread)
    next: Option<&'arena SlabSegmentHdr<'arena>>,
    /// Metadata for each page within the segment
    pages: [SlabSegmentPageMeta<'arena>; PAGES_PER_SEG],
}

impl<'arena> Debug for SlabSegmentHdr<'arena> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SlabSegmentHdr")
            .field("@addr", &(self as *const _))
            .field("owning_tid", &self.owning_tid)
            .field(
                "owning_thread_ty_state",
                &(self.owning_thread_ty_state as *const _),
            )
            .field("next", &self.next.map(|x| x as *const _))
            .field("pages", &self.pages)
            .finish()
    }
}

impl<'arena> SlabSegmentHdr<'arena> {
    pub unsafe fn init_new_seg(self_: *mut Self, owning_tid: u64) {
        (*self_).owning_tid = owning_tid;

        for i in 0..PAGES_PER_SEG {
            SlabSegmentPageMeta::init_page(addr_of_mut!((*self_).pages[i]), self_, i);
            if i != PAGES_PER_SEG - 1 {
                let next_page_meta_ptr = addr_of_mut!((*self_).pages[i + 1]);
                // reborrowing is safe because we *never* make &mut
                (*self_).pages[i].next_page.set(next_page_meta_ptr.as_ref());
            }
        }

        // safety: we initialized everything EXCEPT
        // owning_thread_ty_state which remains UNINIT!
    }

    #[inline]
    pub fn get_hdr_rounded_sz(self_: *const Self) -> usize {
        let t_layout = unsafe { (*self_).owning_thread_ty_state.layout };
        let seg_hdr_size = size_of::<SlabSegmentHdr>();
        let rounded_seg_hdr_sz = roundto(seg_hdr_size, t_layout.align());
        rounded_seg_hdr_sz
    }

    #[inline]
    pub fn get_num_objects(self_: *const Self, is_first_page: bool) -> usize {
        let t_layout = unsafe { (*self_).owning_thread_ty_state.layout };
        let start_unusable = if is_first_page {
            Self::get_hdr_rounded_sz(self_)
        } else {
            0
        };
        let num_objects = num_that_fits(t_layout, ALLOC_PAGE_SZ - start_unusable);
        num_objects
    }

    #[inline]
    pub fn get_addr_of_block(self_: *const Self, page_i: usize, block_i: usize) -> *const u8 {
        assert!(page_i < PAGES_PER_SEG);
        let t_layout = unsafe { (*self_).owning_thread_ty_state.layout };
        let start_unusable = if page_i == 0 {
            Self::get_hdr_rounded_sz(self_)
        } else {
            0
        };
        let start_offs = page_i * ALLOC_PAGE_SZ + start_unusable;
        let num_objects = num_that_fits(t_layout, ALLOC_PAGE_SZ - start_unusable);
        assert!(block_i < num_objects);
        let tot_offs = start_offs + block_i * t_layout.size();
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
struct SlabSegmentPageMeta<'arena> {
    /// Linked list of pages
    next_page: Cell<Option<&'arena SlabSegmentPageMeta<'arena>>>,
    /// List that we allocate from in the fast path
    this_free_list: Cell<Option<&'arena SlabFreeBlock<'arena>>>,
    /// List that we free to from the same thread
    local_free_list: Cell<Option<&'arena SlabFreeBlock<'arena>>>,
    /// List that other threads free onto
    remote_free_list: AtomicUsize,
}

impl<'arena> Debug for SlabSegmentPageMeta<'arena> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SlabSegmentPageMeta")
            .field("@addr", &(self as *const _))
            .field("<first data block>", &unsafe {
                let self_ptr = self as *const SlabSegmentPageMeta<'arena>;
                let self_addr = self as *const _ as usize;
                let seg_addr = self_addr & !(SEGMENT_SZ - 1);
                let seg_ptr = seg_addr as *const SlabSegmentHdr<'arena>;
                let first_page_meta_ptr = addr_of!((*seg_ptr).pages[0]);
                let page_i = self_ptr.offset_from(first_page_meta_ptr) as usize;
                SlabSegmentHdr::get_addr_of_block(seg_ptr, page_i, 0)
            })
            .field("next_page", &self.next_page.get().map(|x| x as *const _))
            .field(
                "this_free_list",
                &self.this_free_list.get().map(|x| x as *const _),
            )
            .field(
                "local_free_list",
                &self.local_free_list.get().map(|x| x as *const _),
            )
            .field(
                "remote_free_list",
                &(self.remote_free_list.load(Ordering::Relaxed) as *const ()),
            )
            .finish()
    }
}

impl<'arena> SlabSegmentPageMeta<'arena> {
    pub unsafe fn init_page(
        self_: *mut Self,
        seg_ptr: *const SlabSegmentHdr<'arena>,
        page_i: usize,
    ) {
        // XXX makes assumptions about niche optimization and layout of Option<&_>

        // this is needed for loom?
        (*self_).remote_free_list = AtomicUsize::new(0);

        // don't need to init much of the meta, but here we set up the free chain of the blocks themselves
        let num_objects = SlabSegmentHdr::get_num_objects(seg_ptr, page_i == 0);
        for block_i in 0..(num_objects - 1) {
            let block_ptr = SlabSegmentHdr::get_addr_of_block(seg_ptr, page_i, block_i);
            let next_block_ptr = SlabSegmentHdr::get_addr_of_block(seg_ptr, page_i, block_i + 1);
            let block_ptr = block_ptr as *mut SlabFreeBlock<'arena>;

            (*block_ptr).next = AtomicU64::new(next_block_ptr as u64);
        }

        // loom crashes without this
        let last_block_ptr = SlabSegmentHdr::get_addr_of_block(seg_ptr, page_i, num_objects - 1);
        let last_block_ptr = last_block_ptr as *mut SlabFreeBlock<'arena>;
        (*last_block_ptr).next = AtomicU64::new(0);

        let block_0_ptr =
            SlabSegmentHdr::get_addr_of_block(seg_ptr, page_i, 0) as *const SlabFreeBlock<'arena>;
        (*self_).this_free_list.set(block_0_ptr.as_ref());
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
        // order: on success, we need to see *all* of the writes to the next pointers
        // that have been set by other threads remote freeing, so order is acquire
        // this will obviously synchronize-with the most recent write.
        // as for previous writes, the intermediate updates to remote_free_list
        // are RmW operations, so they will be part of the release sequence of
        // the previous (now overwritten) writes to remote_free_list.
        // thus this will synchronize-with *all* of those
        let mut prev_remote_free = self.remote_free_list.load(Ordering::Relaxed);
        loop {
            let state = prev_remote_free & 0b11;
            let ptr = prev_remote_free & !0b11;

            // state must be normal
            debug_assert!(state == REMOTE_FREE_FLAGS_STATE_NORMAL);

            if ptr != 0 {
                is_full = false;
            }

            let remote_free_new_ptr_with_flags = if is_full {
                debug_assert!(ptr == 0);
                REMOTE_FREE_FLAGS_STATE_IN_FULL_LIST
            } else {
                REMOTE_FREE_FLAGS_STATE_NORMAL
            };

            match self.remote_free_list.compare_exchange_weak(
                prev_remote_free,
                remote_free_new_ptr_with_flags,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(x) => prev_remote_free = x,
            }
        }

        let remote_free_list_ptr = (prev_remote_free & !0b11) as *const SlabFreeBlock<'arena>;

        if is_full {
            debug_assert!(our_free_list.is_none());
            debug_assert!(remote_free_list_ptr.is_null());
        }

        // this function can only be called when the state is already
        // normal (and this page has been linked back in to the linked list)
        //
        // we _might_ make a state transition here of normal -> in-full-list
        // (which other threads need to be aware of)
        // but there are no valid state transitions that we can miss here
        //
        // the race that *actually* needs to be checked for is "we put this page on the full list,
        // but at the same time another thread frees something (making it not full anymore)
        // but we miss that free and thus never manage to access this block again"
        //
        // this is prevented because:
        // * freeing from the in-full-list state will put something onto the thread delayed free list
        //   (i.e. we have another chance to recover this block the next time we go through the slow path)
        // * freeing from the in-thread-delayed-list state requires moving through the in-full-list state
        // * when freeing from the normal state, setting the state to in-full-list
        //   is atomic with consuming the remote free list
        //
        // this last point is the reason why pointer bit packing is required

        if !remote_free_list_ptr.is_null() {
            // append to end of our free list
            if our_free_list.is_none() {
                // only remote free, none of ours
                self.this_free_list.set(unsafe {
                    // safety: these blocks should definitely belong to our allocation
                    // assuming we didn't mess up
                    remote_free_list_ptr.as_ref()
                });
            } else {
                while let Some(next) = our_free_list.unwrap().load_next() {
                    our_free_list = Some(next);
                }
                our_free_list.unwrap().store_next(unsafe {
                    // safety: these blocks should definitely belong to our allocation
                    // assuming we didn't mess up. we can't data race on next because
                    // current thread owns all of the local free list
                    remote_free_list_ptr.as_ref()
                });
                self.this_free_list.set(our_free_list);
            }
        } else {
            self.this_free_list.set(our_free_list);
        }
    }
}

/// Contents of a slab block when it is free (i.e. free chain)
#[repr(C)]
struct SlabFreeBlock<'arena> {
    // DO NOT MODIFY
    // outside code relies on this layout
    //
    // note that, even though we use atomic operations here,
    // we don't end up with problems if the heap payload doesn't
    // (as long as the external code doesn't *itself* have a data race)
    // because we only hand out allocations to one thread
    // and only allow them to be freed one time from one thread
    // (which may be a different thread), sequenced-before relations
    // plus the synchronizes-with we establish on the free list pointers
    // are sufficient to protect *us*
    next: AtomicU64,
    _p: PhantomData<&'arena SlabFreeBlock<'arena>>,
}
impl<'arena> SlabFreeBlock<'arena> {
    /// Load next pointer with an atomic op (relaxed)
    fn load_next(&'arena self) -> Option<&'arena SlabFreeBlock<'arena>> {
        unsafe {
            // safety: assuming we didn't mess up, next points to something
            // within one of "our" allocations
            let next = self.next.load(Ordering::Relaxed) as usize as *const SlabFreeBlock<'arena>;
            next.as_ref()
        }
    }

    /// Store next pointer with an atomic op (relaxed)
    fn store_next(&'arena self, x: Option<&'arena SlabFreeBlock<'arena>>) {
        let next = match x {
            Some(x) => {
                let x_addr = x as *const _ as usize as u64;
                debug_assert!(x_addr <= 0x7fffffffffffffff);
                x_addr
            }
            None => 0,
        };
        self.next.store(next, Ordering::Relaxed);
    }
}

impl<'arena> Debug for SlabFreeBlock<'arena> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SlabFreeBlock")
            .field("@addr", &(self as *const _))
            .field("next", &(self.next.load(Ordering::Relaxed) as *const ()))
            .finish()
    }
}

#[cfg(test)]
mod tests;
