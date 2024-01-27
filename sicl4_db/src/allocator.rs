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
    collections::HashSet,
    fmt::Debug,
    marker::PhantomData,
    mem::{self, size_of, ManuallyDrop, MaybeUninit},
    ops::Deref,
    ptr::{self, addr_of_mut},
    sync::atomic::Ordering,
};

use crate::loom_testing::*;
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

/// Slab allocator root object
pub struct SlabRoot<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> {
    /// Bitfield, where a `1` bit in position `n` indicates that
    /// a [SlabThreadShard] has been handed out for the nth entry of
    /// [per_thread_state](Self::per_thread_state)
    /// (and it hasn't been dropped yet)
    thread_inuse: AtomicU64,
    /// Actual storage for per-thread data
    per_thread_state: [MaybeUninit<SlabPerThreadState<'arena, CellsTy, WiresTy>>; MAX_THREADS],
    /// Indicates whether or not the state has been initialized
    per_thread_state_inited: [Cell<bool>; MAX_THREADS],
    /// Ensure `'arena` lifetime is invariant
    _p: PhantomData<Cell<&'arena ()>>,
}
// safety: we carefully use atomic operations on thread_inuse
unsafe impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> Sync
    for SlabRoot<'arena, CellsTy, WiresTy>
{
}

impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> Debug
    for SlabRoot<'arena, CellsTy, WiresTy>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut fields = f.debug_struct("SlabRoot");
        fields.field("@addr", &(self as *const _));
        for i in 0..MAX_THREADS {
            if !self.per_thread_state_inited[i].get() {
                fields.field(&format!("per_thread_state[{}]", i), &"<uninit>");
            } else {
                fields.field(&format!("per_thread_state[{}]", i), unsafe {
                    self.per_thread_state[i].assume_init_ref()
                });
            }
        }
        fields.finish()
    }
}

impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> SlabRoot<'arena, CellsTy, WiresTy> {
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
    pub fn new_thread(&'arena self) -> SlabThreadShard<'arena, CellsTy, WiresTy> {
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
            if !self.per_thread_state_inited[allocated_tid].get() {
                SlabPerThreadState::<'arena, CellsTy, WiresTy>::init(
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

    /// Try and get a handle for performing global operations
    pub fn try_lock_global(&'arena self) -> Option<SlabRootGlobalGuard<'arena, CellsTy, WiresTy>> {
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
pub struct SlabRootGlobalGuard<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync>(
    &'arena SlabRoot<'arena, CellsTy, WiresTy>,
    /// prevent this type from being `Sync`
    PhantomData<UnsafeCell<()>>,
);

impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> Debug
    for SlabRootGlobalGuard<'arena, CellsTy, WiresTy>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SlabRootGlobalGuard").field(&self.0).finish()
    }
}

impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> Drop
    for SlabRootGlobalGuard<'arena, CellsTy, WiresTy>
{
    fn drop(&mut self) {
        let root = self.0;
        // ordering: need all manipulation of thread-owned data to stick
        root.thread_inuse.store(0, Ordering::Release);
    }
}

impl<'guard, 'arena, CellsTy: Send + Sync, WiresTy: Send + Sync>
    SlabRootGlobalGuard<'arena, CellsTy, WiresTy>
{
    fn __debug_check_ty_missing_blocks<ThisTy: Send + Sync>(
        thread_i: usize,
        per_thread_per_ty: &'arena SlabPerThreadPerTyState<'arena, ThisTy>,
    ) -> HashSet<usize> {
        let mut all_outstanding_blocks = HashSet::new();
        println!("Checking state for thread {}", thread_i);

        let mut thread_delayed_free_blocks = HashSet::new();
        let delayed_free_block = per_thread_per_ty
            .thread_delayed_free
            .load(Ordering::Relaxed);

        let mut delayed_free_block = if delayed_free_block.is_null() {
            None
        } else {
            unsafe { Some(&*delayed_free_block) }
        };
        while let Some(delayed_free_block_inner) = delayed_free_block {
            println!("thread delayed free: {:?}", delayed_free_block_inner);
            thread_delayed_free_blocks.insert(delayed_free_block_inner as *const _ as usize);
            delayed_free_block = delayed_free_block_inner.next.get();
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

                    this_free = this_free_block.next.get();
                }

                let mut local_free = page.local_free_list.get();
                while let Some(this_free_block) = local_free {
                    println!("Local free list item: {:?}", this_free_block as *const _);
                    let was_outstanding =
                        outstanding_blocks.remove(&(this_free_block as *const _ as usize));

                    if !was_outstanding {
                        panic!("Block not in page or found in multiple free lists!");
                    }

                    local_free = this_free_block.next.get();
                }

                let remote_free = page.remote_free_list.load(Ordering::Relaxed);
                let mut remote_free_ptr = unsafe {
                    let ptr = (remote_free & !0b11) as *const SlabFreeBlock;
                    if ptr.is_null() {
                        None
                    } else {
                        Some(&*ptr)
                    }
                };
                let remote_free_flags = remote_free & 0b11;
                while let Some(this_free_block) = remote_free_ptr {
                    println!("Remote free list item: {:?}", this_free_block as *const _);
                    let was_outstanding =
                        outstanding_blocks.remove(&(this_free_block as *const _ as usize));

                    if !was_outstanding {
                        panic!("Block not in page or found in multiple free lists!");
                    }

                    remote_free_ptr = this_free_block.next.get();
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
    pub fn _debug_check_missing_blocks(&'guard self) -> (HashSet<usize>, HashSet<usize>) {
        let mut all_outstanding_blocks_cells = HashSet::new();
        let mut all_outstanding_blocks_wires = HashSet::new();

        for thread_i in 0..MAX_THREADS {
            if self.0.per_thread_state_inited[thread_i].get() {
                let per_thread = unsafe { &*self.0.per_thread_state[thread_i].as_ptr() };
                println!("~~~~~ Checking netlist cells ~~~~~");
                let outstanding_cells_this_thread =
                    Self::__debug_check_ty_missing_blocks(thread_i, &per_thread.netlist_cells);
                for x in outstanding_cells_this_thread {
                    all_outstanding_blocks_cells.insert(x);
                }
                println!("~~~~~ Checking netlist wires ~~~~~");
                let outstanding_wires_this_thread =
                    Self::__debug_check_ty_missing_blocks(thread_i, &per_thread.netlist_wires);
                for x in outstanding_wires_this_thread {
                    all_outstanding_blocks_wires.insert(x);
                }
            }
        }
        (all_outstanding_blocks_cells, all_outstanding_blocks_wires)
    }
}

/// Slab allocator per-thread state (actual contents)
pub struct SlabPerThreadState<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> {
    /// Identifies this thread
    ///
    /// Current impl: bit position in the [SlabRoot::thread_inuse] bitfield
    tid: u64,
    /// Pointer to the [SlabRoot] this belongs to
    ///
    /// Can be removed if `offset_of!` gets stabilized
    root: &'arena SlabRoot<'arena, CellsTy, WiresTy>,
    /// Manages memory for netlist cells
    netlist_cells: SlabPerThreadPerTyState<'arena, CellsTy>,
    /// Manages memory for netlist wires
    netlist_wires: SlabPerThreadPerTyState<'arena, WiresTy>,
    /// ABA generation counter for cells
    netlist_cell_alloc_gen: Cell<u64>,
    /// ABA generation counter for wires
    netlist_wire_alloc_gen: Cell<u64>,
}
// safety: only one thread can have a SlabThreadShard to access any fields here
unsafe impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> Sync
    for SlabPerThreadState<'arena, CellsTy, WiresTy>
{
}

impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> Debug
    for SlabPerThreadState<'arena, CellsTy, WiresTy>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SlabPerThreadState")
            .field("@addr", &(self as *const _))
            .field("tid", &self.tid)
            .field("root", &self.root)
            .field("netlist_cells", &self.netlist_cells)
            .field("netlist_wires", &self.netlist_wires)
            .field("netlist_cell_alloc_gen", &self.netlist_cell_alloc_gen.get())
            .field("netlist_wire_alloc_gen", &self.netlist_wire_alloc_gen.get())
            .finish()
    }
}

impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync>
    SlabPerThreadState<'arena, CellsTy, WiresTy>
{
    /// Initialize state
    pub unsafe fn init(
        self_: *mut Self,
        tid: u64,
        root: &'arena SlabRoot<'arena, CellsTy, WiresTy>,
    ) {
        SlabPerThreadPerTyState::init(addr_of_mut!((*self_).netlist_cells), tid);
        SlabPerThreadPerTyState::init(addr_of_mut!((*self_).netlist_wires), tid);

        (*self_).tid = tid;
        (*self_).root = root;
        (*self_).netlist_cell_alloc_gen = Cell::new(0);
        (*self_).netlist_wire_alloc_gen = Cell::new(0);

        // safety: we initialized everything
    }

    /// Allocates a netlist cell from this shard
    ///
    /// Does *NOT* initialize any of the resulting memory
    pub fn alloc_netlist_cell(&'arena self) -> (&'arena SlabBlock<'arena, CellsTy>, u64) {
        let cur_gen = self.netlist_cell_alloc_gen.get();
        self.netlist_cell_alloc_gen.set(cur_gen + 1);
        (self.netlist_cells.alloc(self.tid), cur_gen)
    }

    /// Deallocates a netlist cell
    ///
    /// Object must be part of this slab, not already be freed,
    /// and no other references may exist after calling free
    pub unsafe fn free_netlist_cell(&'arena self, obj: &'arena SlabBlock<'arena, CellsTy>) {
        self.netlist_cells.free(self.tid, obj);
    }

    /// Allocates a netlist wire from this shard
    ///
    /// Does *NOT* initialize any of the resulting memory
    pub fn alloc_netlist_wire(&'arena self) -> (&'arena SlabBlock<'arena, WiresTy>, u64) {
        let cur_gen = self.netlist_wire_alloc_gen.get();
        self.netlist_wire_alloc_gen.set(cur_gen + 1);
        (self.netlist_wires.alloc(self.tid), cur_gen)
    }

    /// Deallocates a netlist wire
    ///
    /// Object must be part of this slab, not already be freed,
    /// and no other references may exist after calling free
    pub unsafe fn free_netlist_wire(&'arena self, obj: &'arena SlabBlock<'arena, WiresTy>) {
        self.netlist_wires.free(self.tid, obj);
    }
}

/// Slab allocator per-thread *and* per-type state
struct SlabPerThreadPerTyState<'arena, T: Send + Sync> {
    /// Pointer to segment list (used for global ops) TODO
    segments: Cell<&'arena SlabSegmentHdr<'arena, T>>,
    /// Pointer to head of (non-full) page list
    pages: Cell<&'arena SlabSegmentPageMeta<'arena, T>>,
    /// Pointer to end of (non-full) page list
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
unsafe impl<'arena, T: Send + Sync> Sync for SlabPerThreadPerTyState<'arena, T> {}

impl<'arena, T: Send + Sync> Debug for SlabPerThreadPerTyState<'arena, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SlabPerThreadPerTyState")
            .field("@addr", &(self as *const _))
            .field("segments", &(self.segments.get() as *const _))
            .field("pages", &(self.pages.get() as *const _))
            .field("last_page", &(self.last_page.get() as *const _))
            .field(
                "thread_delayed_free",
                &(self.thread_delayed_free.load(Ordering::SeqCst)),
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

impl<'arena, T: Send + Sync> SlabPerThreadPerTyState<'arena, T> {
    /// Initialize state
    pub unsafe fn init(self_: *mut Self, tid: u64) {
        // alloc initial segment
        let new_initial_seg = SlabSegmentHdr::<'arena, T>::alloc_new_seg(tid);
        let new_initial_seg = unsafe {
            // 😱 this is super dangerous wrt uninit memory
            // hopefully it doesn't break
            (*new_initial_seg).owning_thread_ty_state = mem::transmute(self_);
            (*new_initial_seg).next = None;
            &*new_initial_seg
        };

        unsafe {
            (*self_).segments = Cell::new(new_initial_seg);
            (*self_).pages = Cell::new(&new_initial_seg.pages[0]);
            (*self_).last_page = Cell::new(&new_initial_seg.pages[PAGES_PER_SEG - 1]);
            (*self_).thread_delayed_free = AtomicPtr::new(ptr::null_mut());
        }

        // safety: we initialized everything
    }

    /// Allocate a new segment, link it into segments list,
    /// and make it the *entirety* of the pages list
    ///
    /// Memory unsafety is contained, but this can mess up invariants
    /// (and thus isn't public)
    fn new_seg(&'arena self, tid: u64) {
        let new_seg = SlabSegmentHdr::<'arena, T>::alloc_new_seg(tid);
        let old_seg_head = Some(self.segments.get());
        let new_seg = unsafe {
            (*new_seg).owning_thread_ty_state = self;
            (*new_seg).next = old_seg_head;
            // safety: at this point we've initialized everything
            // *including* the owning_thread_ty_state footgun
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
        tid: u64,
    ) -> (
        &'arena SlabSegmentPageMeta<'arena, T>,
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

        let mut thread_delayed_free = if thread_delayed_free.is_null() {
            None
        } else {
            unsafe {
                // safety: these blocks should definitely belong to our allocation
                // assuming we didn't mess up
                Some(&*thread_delayed_free)
            }
        };

        while let Some(thread_delayed_free_inner) = thread_delayed_free {
            let next = thread_delayed_free_inner.next.get();
            unsafe {
                // safety: just coercing between repr(C) union references
                self.free(tid, mem::transmute(thread_delayed_free_inner))
            }
            thread_delayed_free = next;
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
    pub fn alloc(&'arena self, tid: u64) -> &'arena SlabBlock<'arena, T> {
        let fast_page = self.pages.get();
        let fast_block = fast_page.this_free_list.get();
        let (page, block) = match fast_block {
            Some(x) => (fast_page, x), // fast path
            None => self.alloc_slow(tid),
        };
        page.this_free_list.set(block.next.get());
        unsafe {
            // safety: just coercing between repr(C) union references
            mem::transmute(block)
        }
    }

    /// Deallocates an object
    ///
    /// Object must be part of this slab, not already be freed,
    /// and no other references may exist after calling free
    pub unsafe fn free(&'arena self, tid: u64, obj: &'arena SlabBlock<'arena, T>) {
        let obj_ptr = obj as *const _ as usize;
        let seg_ptr = obj_ptr & !(SEGMENT_SZ - 1);
        let seg = &*(seg_ptr as *const SlabSegmentHdr<'arena, T>);
        let page_i = (obj_ptr - seg_ptr) >> ALLOC_PAGE_SHIFT;

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

            obj.free.next.set(seg.pages[page_i].local_free_list.get());
            seg.pages[page_i].local_free_list.set(Some(&obj.free));
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
                                obj.free.next.set(Some(&*prev_thread_delayed_free));
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
                    let next_block_proper_addr = (prev_remote_free & !0b11) as *const _;
                    obj.free.next.set(Some(&*next_block_proper_addr));
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
pub struct SlabThreadShard<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync>(
    &'arena SlabPerThreadState<'arena, CellsTy, WiresTy>,
    /// prevent this type from being `Sync`
    PhantomData<UnsafeCell<()>>,
);

impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> Debug
    for SlabThreadShard<'arena, CellsTy, WiresTy>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SlabThreadShard").field(&self.0).finish()
    }
}

impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> Deref
    for SlabThreadShard<'arena, CellsTy, WiresTy>
{
    type Target = &'arena SlabPerThreadState<'arena, CellsTy, WiresTy>;

    fn deref<'guard>(&'guard self) -> &'guard &'arena SlabPerThreadState<'arena, CellsTy, WiresTy> {
        &self.0
    }
}

impl<'arena, CellsTy: Send + Sync, WiresTy: Send + Sync> Drop
    for SlabThreadShard<'arena, CellsTy, WiresTy>
{
    fn drop(&mut self) {
        let root = self.0.root;
        let mask = !(1 << self.0.tid);
        // ordering: need all manipulation of thread-owned data to stick
        root.thread_inuse.fetch_and(mask, Ordering::Release);
    }
}

/// Header for each (4 M) segment
#[repr(C)]
struct SlabSegmentHdr<'arena, T: Send + Sync> {
    /// Thread that created this segment and owns its "local" data
    owning_tid: u64,
    /// Per-thread per-type data of the thread that created this
    /// (used for thread delayed free)
    owning_thread_ty_state: &'arena SlabPerThreadPerTyState<'arena, T>,
    /// List of segments (all owned by this thread)
    next: Option<&'arena SlabSegmentHdr<'arena, T>>,
    /// Metadata for each page within the segment
    pages: [SlabSegmentPageMeta<'arena, T>; PAGES_PER_SEG],
}

impl<'arena, T: Send + Sync> Debug for SlabSegmentHdr<'arena, T> {
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

impl<'arena, T: Send + Sync> SlabSegmentHdr<'arena, T> {
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
            // owning_thread_ty_state which remains UNINIT!
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
    pub fn get_num_objects(_: *const Self, is_first_page: bool) -> usize {
        let start_unusable = if is_first_page {
            Self::get_hdr_rounded_sz()
        } else {
            0
        };
        let num_objects = num_that_fits(
            Layout::new::<SlabBlock<T>>(),
            ALLOC_PAGE_SZ - start_unusable,
        );
        num_objects
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
struct SlabSegmentPageMeta<'arena, T: Send + Sync> {
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
unsafe impl<'arena, T: Send + Sync> Sync for SlabSegmentPageMeta<'arena, T> {}

impl<'arena, T: Send + Sync> Debug for SlabSegmentPageMeta<'arena, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SlabSegmentPageMeta")
            .field("@addr", &(self as *const _))
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
                &(self.remote_free_list.load(Ordering::SeqCst) as *const ()),
            )
            .finish()
    }
}

impl<'arena, T: Send + Sync> SlabSegmentPageMeta<'arena, T> {
    pub unsafe fn init_page(
        self_: *mut Self,
        seg_ptr: *const SlabSegmentHdr<'arena, T>,
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
            let block_ptr = block_ptr as *mut SlabBlock<'arena, T>;
            let next_block_ptr = next_block_ptr as *mut SlabFreeBlock<'arena>;

            (*block_ptr).free = ManuallyDrop::new(SlabFreeBlock {
                next: Cell::new(Some(&*next_block_ptr)),
            });
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
                self.this_free_list.set(Some(unsafe {
                    // safety: these blocks should definitely belong to our allocation
                    // assuming we didn't mess up
                    &*remote_free_list_ptr
                }));
            } else {
                while our_free_list.unwrap().next.get().is_some() {
                    our_free_list = our_free_list.unwrap().next.get();
                }
                our_free_list.unwrap().next.set(Some(unsafe {
                    // safety: these blocks should definitely belong to our allocation
                    // assuming we didn't mess up. we can't data race on next because
                    // current thread owns all of the local free list
                    &*remote_free_list_ptr
                }));
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
    free: ManuallyDrop<SlabFreeBlock<'arena>>,
    pub alloced: ManuallyDrop<MaybeUninit<T>>,
}
// safety: this is a wrapper for T
// if exposed outside of this module, the free variant (where the danger lies) is inaccessible
unsafe impl<'arena, T: Send> Send for SlabBlock<'arena, T> {}
unsafe impl<'arena, T: Sync> Sync for SlabBlock<'arena, T> {}

/// Contents of a slab block when it is free (i.e. free chain)
#[repr(C)]
struct SlabFreeBlock<'arena> {
    next: Cell<Option<&'arena SlabFreeBlock<'arena>>>,
}

impl<'arena> Debug for SlabFreeBlock<'arena> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SlabFreeBlock")
            .field("@addr", &(self as *const _))
            .field("next", &self.next.get().map(|x| x as *const _))
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use std::{alloc::Layout, sync::atomic::Ordering};

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
        assert_send::<SlabRoot<'_, u8, ()>>();
        assert_sync::<SlabRoot<'_, u8, ()>>();
    }

    #[test]
    fn ensure_thread_shard_send() {
        assert_send::<SlabThreadShard<'_, u8, ()>>();
    }

    #[cfg(not(loom))]
    #[test]
    fn slab_root_new_thread() {
        let slab = SlabRoot::<u8, ()>::new();

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

    #[cfg(not(loom))]
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

    #[cfg(not(loom))]
    #[test]
    fn slab_basic_single_thread_alloc() {
        let alloc = SlabRoot::<u8, ()>::new();
        let thread_shard = alloc.new_thread();
        let obj_1 = thread_shard.alloc_netlist_cell().0;
        let obj_2 = thread_shard.alloc_netlist_cell().0;
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        assert_eq!(obj_1 as *const _ as usize + 8, obj_2 as *const _ as usize);

        unsafe { thread_shard.free_netlist_cell(obj_2) };
        unsafe { thread_shard.free_netlist_cell(obj_1) };

        unsafe {
            let seg = thread_shard.netlist_cells.segments.get();
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

        drop(thread_shard);
        let (outstanding_blocks_cells, outstanding_blocks_wires) = alloc
            .try_lock_global()
            .unwrap()
            ._debug_check_missing_blocks();
        assert_eq!(outstanding_blocks_cells.len(), 0);
        assert_eq!(outstanding_blocks_wires.len(), 0);
    }

    #[cfg(not(loom))]
    #[test]
    fn slab_basic_fake_remote_free() {
        let alloc = SlabRoot::<u8, ()>::new();
        let thread_shard_0 = alloc.new_thread();
        let obj_1 = thread_shard_0.alloc_netlist_cell().0;
        let obj_2 = thread_shard_0.alloc_netlist_cell().0;
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        let thread_shard_1 = alloc.new_thread();
        unsafe { thread_shard_1.free_netlist_cell(obj_2) };
        unsafe { thread_shard_1.free_netlist_cell(obj_1) };

        unsafe {
            let seg = thread_shard_0.netlist_cells.segments.get();
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

        drop(thread_shard_0);
        drop(thread_shard_1);
        let (outstanding_blocks_cells, outstanding_blocks_wires) = alloc
            .try_lock_global()
            .unwrap()
            ._debug_check_missing_blocks();
        assert_eq!(outstanding_blocks_cells.len(), 0);
        assert_eq!(outstanding_blocks_wires.len(), 0);
    }

    #[cfg(not(loom))]
    #[test]
    fn slab_test_collect_local() {
        let alloc = SlabRoot::<[u8; 30000], ()>::new();
        let thread_shard = alloc.new_thread();
        let obj_1 = thread_shard.alloc_netlist_cell().0;
        let obj_2 = thread_shard.alloc_netlist_cell().0;
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        unsafe { thread_shard.free_netlist_cell(obj_1) };
        unsafe { thread_shard.free_netlist_cell(obj_2) };

        let obj_1_2nd_try = thread_shard.alloc_netlist_cell().0;
        let obj_2_2nd_try = thread_shard.alloc_netlist_cell().0;
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

        drop(thread_shard);
        let (mut outstanding_blocks_cells, outstanding_blocks_wires) = alloc
            .try_lock_global()
            .unwrap()
            ._debug_check_missing_blocks();
        assert!(outstanding_blocks_cells.remove(&(obj_1_2nd_try as *const _ as usize)));
        assert!(outstanding_blocks_cells.remove(&(obj_2_2nd_try as *const _ as usize)));
        assert_eq!(outstanding_blocks_cells.len(), 0);
        assert_eq!(outstanding_blocks_wires.len(), 0);
    }

    #[cfg(not(loom))]
    #[test]
    fn slab_test_collect_remote() {
        let alloc = SlabRoot::<[u8; 30000], ()>::new();
        let thread_shard_0 = alloc.new_thread();
        let obj_1 = thread_shard_0.alloc_netlist_cell().0;
        let obj_2 = thread_shard_0.alloc_netlist_cell().0;
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        let thread_shard_1 = alloc.new_thread();
        unsafe { thread_shard_1.free_netlist_cell(obj_1) };
        unsafe { thread_shard_1.free_netlist_cell(obj_2) };

        let obj_1_2nd_try = thread_shard_0.alloc_netlist_cell().0;
        let obj_2_2nd_try = thread_shard_0.alloc_netlist_cell().0;
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

        drop(thread_shard_0);
        drop(thread_shard_1);
        let (mut outstanding_blocks_cells, outstanding_blocks_wires) = alloc
            .try_lock_global()
            .unwrap()
            ._debug_check_missing_blocks();
        assert!(outstanding_blocks_cells.remove(&(obj_1_2nd_try as *const _ as usize)));
        assert!(outstanding_blocks_cells.remove(&(obj_2_2nd_try as *const _ as usize)));
        assert_eq!(outstanding_blocks_cells.len(), 0);
        assert_eq!(outstanding_blocks_wires.len(), 0);
    }

    #[cfg(not(loom))]
    #[test]
    fn slab_test_collect_both() {
        let alloc = SlabRoot::<[u8; 30000], ()>::new();
        let thread_shard_0 = alloc.new_thread();
        let obj_1 = thread_shard_0.alloc_netlist_cell().0;
        let obj_2 = thread_shard_0.alloc_netlist_cell().0;
        println!("Allocated obj 1 {:?}", obj_1 as *const _);
        println!("Allocated obj 2 {:?}", obj_2 as *const _);

        let thread_shard_1 = alloc.new_thread();
        unsafe { thread_shard_0.free_netlist_cell(obj_1) };
        unsafe { thread_shard_1.free_netlist_cell(obj_2) };

        let obj_1_2nd_try = thread_shard_0.alloc_netlist_cell().0;
        let obj_2_2nd_try = thread_shard_0.alloc_netlist_cell().0;
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

        drop(thread_shard_0);
        drop(thread_shard_1);
        let (mut outstanding_blocks_cells, outstanding_blocks_wires) = alloc
            .try_lock_global()
            .unwrap()
            ._debug_check_missing_blocks();
        assert!(outstanding_blocks_cells.remove(&(obj_1_2nd_try as *const _ as usize)));
        assert!(outstanding_blocks_cells.remove(&(obj_2_2nd_try as *const _ as usize)));
        assert_eq!(outstanding_blocks_cells.len(), 0);
        assert_eq!(outstanding_blocks_wires.len(), 0);
    }

    #[cfg(not(loom))]
    #[test]
    fn slab_test_new_seg() {
        let alloc = SlabRoot::<[u8; 30000], ()>::new();
        let thread_shard = alloc.new_thread();
        let mut things = Vec::new();
        for i in 0..129 {
            let obj = thread_shard.alloc_netlist_cell().0;
            println!("Allocated obj {:3} {:?}", i, obj as *const _);
            things.push(obj);
        }

        for i in 0..129 {
            let obj = things[i];
            unsafe { thread_shard.free_netlist_cell(obj) };
            println!("Freed obj {:3}", i);
        }

        let mut things2 = Vec::new();
        for i in 0..129 {
            let obj = thread_shard.alloc_netlist_cell().0;
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

        drop(thread_shard);
        let (mut outstanding_blocks_cells, outstanding_blocks_wires) = alloc
            .try_lock_global()
            .unwrap()
            ._debug_check_missing_blocks();
        for x in things2 {
            assert!(outstanding_blocks_cells.remove(&(x as *const _ as usize)));
        }
        assert_eq!(outstanding_blocks_cells.len(), 0);
        assert_eq!(outstanding_blocks_wires.len(), 0);
    }

    #[cfg(not(loom))]
    #[test]
    fn slab_test_remote_free() {
        let alloc = SlabRoot::<[u8; 30000], ()>::new();
        let thread_shard_0 = alloc.new_thread();
        let thread_shard_1 = alloc.new_thread();
        let mut things = Vec::new();
        for i in 0..129 {
            let obj = thread_shard_0.alloc_netlist_cell().0;
            println!("Allocated obj {:3} {:?}", i, obj as *const _);
            things.push(obj);
        }

        for i in 0..129 {
            let obj = things[i];
            unsafe { thread_shard_1.free_netlist_cell(obj) };
            println!("Freed obj {:3}", i);
        }

        // delayed free list tests
        {
            let seg1 = thread_shard_0.netlist_cells.segments.get();
            let seg0 = seg1.next.unwrap();

            for page_i in 0..64 {
                let remote_free_list = seg0.pages[page_i].remote_free_list.load(Ordering::SeqCst);

                // each one of these should contain one block here and one block on the thread delayed free list
                assert!(remote_free_list & 0b11 == REMOTE_FREE_FLAGS_STATE_IN_DELAYED_FREE_LIST);

                assert_eq!(
                    remote_free_list & !0b11,
                    things[page_i * 2 + 1] as *const _ as usize
                );
                unsafe {
                    assert_eq!(*((remote_free_list & !0b11) as *const usize), 0);
                }
            }
            let remote_free_list_seg1_pg0 = seg1.pages[0].remote_free_list.load(Ordering::SeqCst);
            assert!(remote_free_list_seg1_pg0 & 0b11 == REMOTE_FREE_FLAGS_STATE_NORMAL);
            assert_eq!(
                remote_free_list_seg1_pg0 & !0b11,
                things[128] as *const _ as usize
            );
        }

        let mut test_thread_delayed_item = thread_shard_0
            .netlist_cells
            .thread_delayed_free
            .load(Ordering::SeqCst) as *const usize;
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
            let obj = thread_shard_0.alloc_netlist_cell().0;
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

        drop(thread_shard_0);
        drop(thread_shard_1);
        let (mut outstanding_blocks_cells, outstanding_blocks_wires) = alloc
            .try_lock_global()
            .unwrap()
            ._debug_check_missing_blocks();
        for x in things2 {
            assert!(outstanding_blocks_cells.remove(&(x as *const _ as usize)));
        }
        assert_eq!(outstanding_blocks_cells.len(), 0);
        assert_eq!(outstanding_blocks_wires.len(), 0);
    }

    #[cfg(loom)]
    #[test]
    fn slab_loom_new_thread() {
        loom::model(|| {
            let alloc = &*Box::leak(Box::new(
                SlabRoot::<'static, [u8; 30000], [u8; 30000]>::new(),
            ));

            let t0 = loom::thread::spawn(move || {
                {
                    let thread_shard_0 = alloc.new_thread();
                    assert!(thread_shard_0.tid == 0 || thread_shard_0.tid == 1);
                    assert!(alloc.per_thread_state_inited[thread_shard_0.tid as usize].get());
                }
                {
                    let thread_shard_0 = alloc.new_thread();
                    assert!(thread_shard_0.tid == 0 || thread_shard_0.tid == 1);
                    assert!(alloc.per_thread_state_inited[thread_shard_0.tid as usize].get());
                }
            });

            let t1 = loom::thread::spawn(move || {
                {
                    let thread_shard_1 = alloc.new_thread();
                    assert!(thread_shard_1.tid == 0 || thread_shard_1.tid == 1);
                    assert!(alloc.per_thread_state_inited[thread_shard_1.tid as usize].get());
                }
                {
                    let thread_shard_1 = alloc.new_thread();
                    assert!(thread_shard_1.tid == 0 || thread_shard_1.tid == 1);
                    assert!(alloc.per_thread_state_inited[thread_shard_1.tid as usize].get());
                }
            });

            t0.join().unwrap();
            t1.join().unwrap();

            assert_eq!(alloc.thread_inuse.load(Ordering::SeqCst), 0);
        })
    }

    #[cfg(loom)]
    #[test]
    fn slab_loom_smoke_test() {
        loom::model(|| {
            let alloc = &*Box::leak(Box::new(
                SlabRoot::<'static, [u8; 30000], [u8; 30000]>::new(),
            ));
            let (sender, receiver) = loom::sync::mpsc::channel();

            let n_objs = 5;

            let t0 = loom::thread::spawn(move || {
                let thread_shard_0 = alloc.new_thread();
                let mut alloc_history = Vec::new();
                let mut prev = None;
                for i in 0..n_objs {
                    let obj = thread_shard_0.alloc_netlist_cell().0;
                    let obj_addr = obj as *const _ as usize;
                    alloc_history.push(obj_addr);
                    unsafe {
                        let obj_ = obj.alloced.as_ptr() as *mut [u8; 30000];
                        (*obj_)[0] = 0xef;
                        (*obj_)[1] = 0xbe;
                        (*obj_)[2] = 0xad;
                        (*obj_)[3] = 0xde;
                        (*obj_)[4] = i as u8;
                        (*obj_)[5] = (i >> 8) as u8;
                        (*obj_)[6] = (i >> 16) as u8;
                        (*obj_)[7] = (i >> 24) as u8;
                    }
                    // in range
                    assert!(
                        obj_addr
                            >= thread_shard_0.netlist_cells.segments.get() as *const _ as usize
                    );
                    assert!(
                        obj_addr
                            < thread_shard_0.netlist_cells.segments.get() as *const _ as usize
                                + SEGMENT_SZ
                    );

                    // delay freeing by 1
                    if let Some(prev) = prev {
                        let prev_addr = prev as *const _ as usize;
                        // check that we didn't dup allocate a block
                        assert!(obj_addr != prev_addr);
                        sender.send(prev).unwrap();
                    }
                    prev = Some(obj);
                }
                sender.send(prev.unwrap()).unwrap();
            });

            let t1 = loom::thread::spawn(move || {
                let thread_shard_1 = alloc.new_thread();
                for i in 0..n_objs {
                    let obj = receiver.recv().unwrap();
                    unsafe {
                        let obj_ = obj.alloced.as_ptr() as *const u64;
                        assert_eq!(*obj_, (i << 32) | 0xdeadbeef);
                        thread_shard_1.free_netlist_cell(obj)
                    }
                }
            });

            t0.join().unwrap();
            t1.join().unwrap();

            let (outstanding_blocks_cells, outstanding_blocks_wires) = alloc
                .try_lock_global()
                .unwrap()
                ._debug_check_missing_blocks();
            assert_eq!(outstanding_blocks_cells.len(), 0);
            assert_eq!(outstanding_blocks_wires.len(), 0);
        })
    }

    #[cfg(not(loom))]
    #[test]
    fn slab_not_loom_smoke_test() {
        let alloc = &*Box::leak(Box::new(
            SlabRoot::<'static, [u8; 30000], [u8; 30000]>::new(),
        ));
        let (sender, receiver) = std::sync::mpsc::channel();

        let n_objs = 10_000_000;

        let t0 = std::thread::spawn(move || {
            let thread_shard_0 = alloc.new_thread();
            let mut alloc_history = Vec::new();
            let mut prev = None;
            for i in 0..n_objs {
                let obj = thread_shard_0.alloc_netlist_cell().0;
                let obj_addr = obj as *const _ as usize;
                unsafe {
                    let obj_ = obj.alloced.as_ptr() as *mut [u8; 30000];
                    (*obj_)[0] = 0xef;
                    (*obj_)[1] = 0xbe;
                    (*obj_)[2] = 0xad;
                    (*obj_)[3] = 0xde;
                    (*obj_)[4] = i as u8;
                    (*obj_)[5] = (i >> 8) as u8;
                    (*obj_)[6] = (i >> 16) as u8;
                    (*obj_)[7] = (i >> 24) as u8;
                }
                alloc_history.push(obj_addr);
                // in range
                let mut in_range = false;
                let mut seg = thread_shard_0.netlist_cells.segments.get();
                loop {
                    if (obj_addr >= seg as *const _ as usize)
                        && (obj_addr < seg as *const _ as usize + SEGMENT_SZ)
                    {
                        in_range = true;
                        break;
                    }

                    if seg.next.is_some() {
                        seg = seg.next.unwrap();
                    } else {
                        break;
                    }
                }
                assert!(in_range);

                // delay freeing by 1
                if let Some(prev) = prev {
                    let prev_addr = prev as *const _ as usize;
                    // check that we didn't dup allocate a block
                    assert!(obj_addr != prev_addr);
                    sender.send(prev).unwrap();
                }
                prev = Some(obj);
            }
            sender.send(prev.unwrap()).unwrap();
        });

        let t1 = std::thread::spawn(move || {
            let thread_shard_1 = alloc.new_thread();
            for i in 0..n_objs {
                let obj = receiver.recv().unwrap();
                unsafe {
                    let obj_ = obj.alloced.as_ptr() as *const u64;
                    assert_eq!(*obj_, (i << 32) | 0xdeadbeef);
                    thread_shard_1.free_netlist_cell(obj)
                }
            }
        });

        t0.join().unwrap();
        t1.join().unwrap();

        let (outstanding_blocks_cells, outstanding_blocks_wires) = alloc
            .try_lock_global()
            .unwrap()
            ._debug_check_missing_blocks();
        assert_eq!(outstanding_blocks_cells.len(), 0);
        assert_eq!(outstanding_blocks_wires.len(), 0);
    }

    #[cfg(not(loom))]
    #[test]
    fn slab_global_lock_test() {
        let alloc = SlabRoot::<u8, ()>::new();
        let thread_shard_0 = alloc.new_thread();
        let thread_shard_1 = alloc.new_thread();

        assert!(alloc.try_lock_global().is_none());

        drop(thread_shard_0);
        assert!(alloc.try_lock_global().is_none());

        drop(thread_shard_1);
        let global = alloc.try_lock_global();
        assert!(global.is_some());

        let global = global.unwrap();
        assert_eq!(alloc.thread_inuse.load(Ordering::SeqCst), u64::MAX);

        drop(global);
        assert_eq!(alloc.thread_inuse.load(Ordering::SeqCst), 0);
        let _thread_shard_0_again = alloc.new_thread();
    }

    #[cfg(not(loom))]
    #[test]
    #[should_panic]
    fn slab_global_lock_blocks_threads_test() {
        let alloc = SlabRoot::<u8, ()>::new();
        let _global = alloc.try_lock_global().unwrap();

        let _thread_shard = alloc.new_thread();
    }

    #[cfg(not(loom))]
    #[test]
    fn slab_separate_cells_wires_smoke_test() {
        let alloc = SlabRoot::<[u8; 30000], [u8; 29999]>::new();
        let thread_shard = alloc.new_thread();

        let cell_obj = thread_shard.alloc_netlist_cell().0;
        let wire_obj = thread_shard.alloc_netlist_wire().0;
        println!("Allocated cell obj {:?}", cell_obj as *const _);
        println!("Allocated wire obj {:?}", wire_obj as *const _);

        // in range
        let cell_obj_addr = cell_obj as *const _ as usize;
        assert!(cell_obj_addr >= thread_shard.netlist_cells.segments.get() as *const _ as usize);
        assert!(
            cell_obj_addr
                < thread_shard.netlist_cells.segments.get() as *const _ as usize + SEGMENT_SZ
        );
        let wire_obj_addr = wire_obj as *const _ as usize;
        assert!(wire_obj_addr >= thread_shard.netlist_wires.segments.get() as *const _ as usize);
        assert!(
            wire_obj_addr
                < thread_shard.netlist_wires.segments.get() as *const _ as usize + SEGMENT_SZ
        );

        drop(thread_shard);
        let (outstanding_blocks_cells, outstanding_blocks_wires) = alloc
            .try_lock_global()
            .unwrap()
            ._debug_check_missing_blocks();
        assert_eq!(outstanding_blocks_cells.len(), 1);
        assert_eq!(outstanding_blocks_wires.len(), 1);
        assert!(outstanding_blocks_cells.contains(&cell_obj_addr));
        assert!(outstanding_blocks_wires.contains(&wire_obj_addr));

        // now do a free
        let thread_shard = alloc.new_thread();
        unsafe {
            thread_shard.free_netlist_cell(cell_obj);
            thread_shard.free_netlist_wire(wire_obj);
        }
        println!("Did a free!");
        drop(thread_shard);
        let (outstanding_blocks_cells, outstanding_blocks_wires) = alloc
            .try_lock_global()
            .unwrap()
            ._debug_check_missing_blocks();
        assert_eq!(outstanding_blocks_cells.len(), 0);
        assert_eq!(outstanding_blocks_wires.len(), 0);
    }
}
