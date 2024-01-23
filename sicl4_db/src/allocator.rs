//! Custom slab-based memory allocator
//!
//! This is a custom concurrent slab memory allocator inspired by the
//! [sharded_slab](https://docs.rs/sharded-slab/latest/sharded_slab/implementation/index.html)
//! crate, which is in turn inspired by the
//! [Mimalloc](https://www.microsoft.com/en-us/research/uploads/prod/2019/06/mimalloc-tr-v1.pdf)
//! allocator from Microsoft Research.

use std::{
    cell::Cell,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    sync::atomic::{AtomicU64, Ordering},
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
const MAX_THREADS: usize = 64;
const _: () = assert!(MAX_THREADS <= 64);

#[derive(Debug)]
pub struct SlabRoot<'arena> {
    /// Bitfield, where a `1` bit in position `n` indicates that
    /// a [SlabThreadShard] has been handed out for the nth entry of
    /// [per_thread_state](Self::per_thread_state)
    /// (and it hasn't been dropped yet)
    thread_inuse: AtomicU64,
    per_thread_state: [SlabPerThreadState<'arena>; MAX_THREADS],
    /// Ensure `'arena` lifetime is invariant
    _p: PhantomData<Cell<&'arena ()>>,
}
// safety: we carefully use atomic operations on thread_inuse
unsafe impl<'arena> Sync for SlabRoot<'arena> {}

impl<'arena> SlabRoot<'arena> {
    pub fn new() -> Self {
        // safety: standard array per-element init, where a MaybeUninit doesn't require init
        let mut per_thread_state: [MaybeUninit<SlabPerThreadState>; MAX_THREADS] =
            unsafe { MaybeUninit::uninit().assume_init() };

        // use the trick from the shared-arena crate
        // (except corrected, see https://github.com/sebastiencs/shared-arena/issues/6)
        // in order to push the safety requirement down to SlabPerThreadState::init
        for i in 0..MAX_THREADS {
            let _ = SlabPerThreadState::init(&mut per_thread_state[i]);
        }

        Self {
            thread_inuse: AtomicU64::new(0),
            per_thread_state: unsafe { mem::transmute(per_thread_state) },
            _p: PhantomData,
        }
    }

    pub fn new_thread(&'arena self) -> SlabThreadShard<'arena> {
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
        thread_state
    }
}

#[derive(Debug)]
pub struct SlabPerThreadState<'arena> {
    _hack_for_tests_for_now: u8,
    /// Ensure `'arena` lifetime is invariant
    _p: PhantomData<Cell<&'arena ()>>,
}

impl<'arena> SlabPerThreadState<'arena> {
    pub fn init(self_: &mut MaybeUninit<Self>) -> &mut Self {
        unsafe {
            let p = self_.as_mut_ptr();
            (*p)._hack_for_tests_for_now = 0;
            (*p)._p = PhantomData;
            // safety: we initialized everything
            &mut *p
        }
    }
}

type SlabThreadShard<'arena> = &'arena SlabPerThreadState<'arena>;

#[cfg(test)]
mod tests {
    use std::sync::atomic::Ordering;

    use super::SlabRoot;

    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}

    #[test]
    fn ensure_slab_root_send_sync() {
        assert_send::<SlabRoot<'_>>();
        assert_sync::<SlabRoot<'_>>();
    }

    #[test]
    fn slab_root_new_thread() {
        let slab = SlabRoot::new();

        let shard1 = slab.new_thread();
        assert_eq!(slab.thread_inuse.load(Ordering::SeqCst), 0b1);
        unsafe {
            assert_eq!(slab.per_thread_state.as_ptr().offset(0), shard1 as *const _);
        }
        let shard2 = slab.new_thread();
        assert_eq!(slab.thread_inuse.load(Ordering::SeqCst), 0b11);
        unsafe {
            assert_eq!(slab.per_thread_state.as_ptr().offset(1), shard2 as *const _);
        }
    }
}

/*//!
//! There are a number of relatively-minor changes made relative to the
//! `sharded_slab` crate, but the most significant change is that the code
//! here has tighter integration between memory allocation and object locking.
//! Some notes as to why have been written
//! [here](https://arcanenibble.github.io/drafts/parallel-capable-netlist-data-structures-part-2.html)
//! (TODO CHANGE THIS WHEN PUBLISHED).*/

/*// FIXME: *const vs *mut variance???
// FIXME: NotNull etc annotation?

const SEGMENT_SZ: usize = 4 * 1024 * 1024; // 4 M
const SEGMENT_LAYOUT: Layout = match Layout::from_size_align(SEGMENT_SZ, SEGMENT_SZ) {
    Ok(x) => x,
    Err(_) => panic!("Invalid SEGMENT_SZ"),
};
const ALLOC_PAGE_SHIFT: usize = 16; // 64 K
const ALLOC_PAGE_SZ: usize = 1 << ALLOC_PAGE_SHIFT;
const PAGES_PER_SEG: usize = SEGMENT_SZ / ALLOC_PAGE_SZ;

use std::{
    alloc::Layout,
    marker::PhantomData,
    mem::size_of,
    ptr::{addr_of, addr_of_mut},
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::util::*;

#[derive(Debug)]
pub struct SlabAlloc<T: Send> {
    next_tid: AtomicUsize,
    _p: PhantomData<T>,
}

impl<T: Send> SlabAlloc<T> {
    pub fn new() -> Self {
        let _t_layout = Layout::new::<T>().pad_to_align();
        // TODO: checks that this will work okay

        Self {
            next_tid: AtomicUsize::new(0),
            _p: PhantomData,
        }
    }

    pub fn new_shard(&self) -> SlabThreadState<T> {
        let new_tid = self.next_tid.fetch_add(1, Ordering::Relaxed);
        // TODO(?): panic on tid overflow
        SlabThreadState::new(new_tid)
    }
}

// XXX didn't necessarily think this through always?
unsafe impl<T: Send> Sync for SlabAlloc<T> {}

#[derive(Debug)]
pub struct SlabThreadState<T: Send> {
    tid: usize,
    alloc_generation: usize,
    segments_head: *mut SlabSegmentHdr,
    _p: PhantomData<T>,
}

unsafe impl<T: Send> Send for SlabThreadState<T> {}

impl<T: Send> SlabThreadState<T> {
    pub fn new(tid: usize) -> Self {
        let seg = unsafe {
            // xxx make really sure that allocating all-zeros won't make UB
            let seg = std::alloc::alloc_zeroed(SEGMENT_LAYOUT) as *mut SlabSegmentHdr;
            (*seg).owning_tid = tid;

            println!("Allocated segment @ {:?} owned by thread {}", seg, tid);

            let seg_hdr_size = size_of::<SlabSegmentHdr>();
            println!("Segment header size is {}", seg_hdr_size);

            let block_with_t_layout = Layout::new::<SlabBlock<T>>().pad_to_align();
            println!("Block type layout {:?}", block_with_t_layout);

            let rounded_seg_hdr_sz = divroundup(seg_hdr_size, block_with_t_layout.align());

            for page_i in 0..PAGES_PER_SEG {
                let page_ptr = if page_i == 0 {
                    (seg as *mut u8).offset(rounded_seg_hdr_sz as isize)
                } else {
                    (seg as *mut u8).offset((page_i * ALLOC_PAGE_SZ) as isize)
                };
                println!("Page {} addr is {:?}", page_i, page_ptr);

                let num_objects = if page_i == 0 {
                    (ALLOC_PAGE_SZ - rounded_seg_hdr_sz) / block_with_t_layout.size()
                } else {
                    ALLOC_PAGE_SZ / block_with_t_layout.size()
                };
                println!("\tfits {} objects", num_objects);

                for obj_i in 0..(num_objects - 1) {
                    let block_ptr =
                        (page_ptr as *mut u8).offset((obj_i * block_with_t_layout.size()) as isize);
                    let block_ptr = block_ptr as *mut SlabBlock<*mut SlabBlock<*mut ()>>;
                    let next_block_ptr = (page_ptr as *mut u8)
                        .offset(((obj_i + 1) * block_with_t_layout.size()) as isize);
                    (*block_ptr).payload = next_block_ptr as *mut SlabBlock<*mut ()>;
                }

                (*seg).pages[page_i].this_free_list = page_ptr as *mut SlabBlock<*mut ()>;
            }

            // print!("{}", _debug_hexdump(seg as *const u8, SEGMENT_SZ).unwrap());

            seg
        };

        Self {
            tid,
            alloc_generation: 0,
            segments_head: seg,
            _p: PhantomData,
        }
    }

    pub fn alloc(&mut self) -> *mut SlabBlock<T> {
        unsafe {
            let seg = self.segments_head;
            // XXX search each page???
            let page = addr_of_mut!((*seg).pages[0]);
            // XXX wtf is going on with lifetimes?
            let block_ptr = (*page).this_free_list;
            if block_ptr.is_null() {
                todo!()
            }
            let block_next = (*block_ptr).payload as *mut SlabBlock<*mut ()>;
            (*page).this_free_list = block_next;
            // XXX initialization halp
            block_ptr as *mut SlabBlock<T>
        }
    }

    pub unsafe fn free(&mut self, p: *mut SlabBlock<T>) {
        let p_usz = p as usize;
        let seg_usz = p_usz & !(SEGMENT_SZ - 1);
        let seg = seg_usz as *mut SlabSegmentHdr;
        let page_i = (p_usz - seg_usz) >> ALLOC_PAGE_SHIFT;

        // we don't allow freeing null?

        println!("Freeing {:?}", p);
        println!("Seg is {:?}", seg);
        println!("Page # {}", page_i);

        if self.tid == (*seg).owning_tid {
            // local free
            let p_as_free = p as *mut SlabBlock<*mut SlabBlock<*mut ()>>;
            (*p_as_free).payload = (*seg).pages[page_i].local_free_list;
            (*seg).pages[page_i].local_free_list = p as *mut SlabBlock<*mut ()>;
        } else {
            // remote free
            todo!()
        }

        print!("{}", _debug_hexdump(seg as *const u8, SEGMENT_SZ).unwrap());
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct SlabSegmentHdr {
    owning_tid: usize,
    pages: [SlabSegmentPageMeta; PAGES_PER_SEG],
}

#[repr(C)]
#[derive(Debug)]
pub struct SlabSegmentPageMeta {
    this_free_list: *mut SlabBlock<*mut ()>,
    local_free_list: *mut SlabBlock<*mut ()>,
    remote_free_list: *mut SlabBlock<*mut ()>,
}

#[repr(C)]
#[derive(Debug)]
pub struct SlabBlock<T> {
    rwlock: AtomicUsize,
    // XXX optimization do we need this on a free block?
    generation: usize,
    payload: T,
}

#[cfg(test)]
mod tests {
    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}

    use std::cell::UnsafeCell;

    use super::*;

    #[test]
    fn ensure_slab_alloc_send_sync() {
        assert_send::<SlabAlloc<UnsafeCell<()>>>();
        assert_sync::<SlabAlloc<UnsafeCell<()>>>();
    }

    #[test]
    fn ensure_thread_state_send() {
        assert_send::<SlabThreadState<UnsafeCell<()>>>();
    }

    #[test]
    fn basic_single_thread_alloc() {
        let alloc = SlabAlloc::<u8>::new();
        let mut thread_shard = alloc.new_shard();
        let obj_1 = thread_shard.alloc();
        let obj_2 = thread_shard.alloc();
        println!("Allocated obj 1 {:?}", obj_1);
        println!("Allocated obj 2 {:?}", obj_2);

        unsafe { thread_shard.free(obj_2) };
        unsafe { thread_shard.free(obj_1) };

        // XXX we should be testing things automatically and not with eyeballs
    }
}
*/
