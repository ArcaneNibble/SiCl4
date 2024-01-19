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
