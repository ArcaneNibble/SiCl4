//! Custom slab-based memory allocator
//!
//! This is a custom concurrent slab memory allocator inspired by the
//! [sharded_slab](https://docs.rs/sharded-slab/latest/sharded_slab/implementation/index.html)
//! crate, which is in turn inspired by the
//! [Mimalloc](https://www.microsoft.com/en-us/research/uploads/prod/2019/06/mimalloc-tr-v1.pdf)
//! allocator from Microsoft Research.
//!
//! There are a number of relatively-minor changes made relative to the
//! `sharded_slab` crate, but the most significant change is that the code
//! here has tighter integration between memory allocation and object locking.
//! Some notes as to why have been written
//! [here](https://arcanenibble.github.io/drafts/parallel-capable-netlist-data-structures-part-2.html)
//! (TODO CHANGE THIS WHEN PUBLISHED).

// FIXME: *const vs *mut variance???
// FIXME: NotNull etc annotation?

const SEGMENT_SZ: usize = 4 * 1024 * 1024;
const SEGMENT_LAYOUT: Layout = match Layout::from_size_align(SEGMENT_SZ, SEGMENT_SZ) {
    Ok(x) => x,
    Err(_) => panic!("Invalid SEGMENT_SZ"),
};
const ALLOC_PAGE_SZ: usize = 64 * 1024;

use std::{
    alloc::Layout,
    marker::PhantomData,
    mem::size_of,
    sync::atomic::{AtomicUsize, Ordering},
};

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
    fn new(tid: usize) -> Self {
        let seg = unsafe {
            // xxx make really sure that allocating all-zeros won't make UB
            let seg = std::alloc::alloc_zeroed(SEGMENT_LAYOUT) as *mut SlabSegmentHdr;
            (*seg).owning_tid = tid;

            println!("Allocated segment @ {:?} owned by thread {}", seg, tid);

            let _seg_hdr_size = size_of::<SlabSegmentHdr>();
            println!("Segment header size is {}", _seg_hdr_size);

            seg
        };

        Self {
            tid,
            alloc_generation: 0,
            segments_head: seg,
            _p: PhantomData,
        }
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct SlabSegmentHdr {
    owning_tid: usize,
    pages: [SlabSegmentPageMeta; SEGMENT_SZ / ALLOC_PAGE_SZ],
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
        let alloc = SlabAlloc::<u32>::new();
        let thread_shard = alloc.new_shard();
    }
}
