use std::{alloc::Layout, sync::atomic::Ordering};

use crate::util::_debug_hexdump;

use super::*;

fn assert_send<T: Send>() {}
fn assert_sync<T: Sync>() {}

struct JustU8Mapper {}
impl TypeMapper for JustU8Mapper {
    type BinsArrayTy<T> = [T; 1];
    const LAYOUTS: &'static [&'static [Layout]] = &[&[Layout::new::<u8>()]];
}
unsafe impl TypeMappable<JustU8Mapper> for u8 {
    const I: usize = 0;
}

struct JustBigArrayMapper {}
impl TypeMapper for JustBigArrayMapper {
    type BinsArrayTy<T> = [T; 1];
    const LAYOUTS: &'static [&'static [Layout]] = &[&[Layout::new::<[u8; 30000]>()]];
}
unsafe impl TypeMappable<JustBigArrayMapper> for [u8; 30000] {
    const I: usize = 0;
}

struct TwoBigArrayMapper {}
impl TypeMapper for TwoBigArrayMapper {
    type BinsArrayTy<T> = [T; 2];
    const LAYOUTS: &'static [&'static [Layout]] = &[
        &[Layout::new::<[u8; 30000]>()],
        &[Layout::new::<[u8; 29999]>()],
    ];
}
unsafe impl TypeMappable<TwoBigArrayMapper> for [u8; 30000] {
    const I: usize = 0;
}
unsafe impl TypeMappable<TwoBigArrayMapper> for [u8; 29999] {
    const I: usize = 1;
}

#[cfg(not(loom))]
#[test]
fn alloc_layout_compute() {
    struct LayoutComputeTest {}
    impl TypeMapper for LayoutComputeTest {
        type BinsArrayTy<T> = [T; 2];

        const LAYOUTS: &'static [&'static [Layout]] = &[
            &[Layout::new::<[u8; 9]>()],
            &[match Layout::from_size_align(1, 32) {
                Ok(x) => x,
                Err(_) => unreachable!(),
            }],
        ];
    }

    let slab = SlabRoot::<LayoutComputeTest>::new();
    let shard1 = slab.new_thread();

    assert_eq!(
        shard1.per_ty_state[0].layout,
        Layout::from_size_align(16, 8).unwrap()
    );
    assert_eq!(
        shard1.per_ty_state[1].layout,
        Layout::from_size_align(32, 32).unwrap()
    );
}

#[test]
fn test_num_that_fits() {
    assert_eq!(num_that_fits(Layout::new::<u32>(), 256), 256 / 4);
    #[repr(align(4))]
    struct WithPadding(#[allow(dead_code)] u8);
    assert_eq!(num_that_fits(Layout::new::<WithPadding>(), 256), 256 / 4);
}

#[test]
fn ensure_slab_root_send_sync() {
    assert_send::<SlabRoot<'_, JustU8Mapper>>();
    assert_sync::<SlabRoot<'_, JustU8Mapper>>();
}

#[test]
fn ensure_thread_shard_send() {
    assert_send::<SlabThreadShard<'_, JustU8Mapper>>();
}

#[cfg(not(loom))]
#[test]
fn slab_root_new_thread() {
    let slab = SlabRoot::<JustU8Mapper>::new();

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
    let slab = SlabRoot::<JustU8Mapper>::new();
    let shard = slab.new_thread();
    drop(shard);
    unsafe {
        let seg = (*((&*slab.per_thread_state[0].get()).as_ptr())).per_ty_state[0]
            .segments
            .get();
        print!(
            "{}",
            _debug_hexdump(seg as *const _ as *const u8, SEGMENT_SZ).unwrap()
        );
    }
}

#[cfg(not(loom))]
#[test]
fn slab_pointer_manip_check() {
    let slab = SlabRoot::<JustU8Mapper>::new();
    let shard = slab.new_thread();
    drop(shard);
    let x = unsafe {
        (*((&*slab.per_thread_state[0].get()).as_ptr())).per_ty_state[0]
            .segments
            .get()
    };
    // we have min sz and align of 8

    // first object
    assert_eq!(
        SlabSegmentHdr::get_addr_of_block(x, 0, 0) as usize,
        (x as *const _ as usize) + SlabSegmentHdr::get_hdr_rounded_sz(x)
    );
    assert_eq!(
        SlabSegmentHdr::get_addr_of_block(x, 1, 0) as usize,
        (x as *const _ as usize) + ALLOC_PAGE_SZ
    );
    assert_eq!(
        SlabSegmentHdr::get_addr_of_block(x, 2, 0) as usize,
        (x as *const _ as usize) + ALLOC_PAGE_SZ * 2
    );
    assert_eq!(
        SlabSegmentHdr::get_addr_of_block(x, 63, 0) as usize,
        (x as *const _ as usize) + ALLOC_PAGE_SZ * 63
    );

    // one object in
    assert_eq!(
        SlabSegmentHdr::get_addr_of_block(x, 0, 1) as usize,
        (x as *const _ as usize) + SlabSegmentHdr::get_hdr_rounded_sz(x) + 8
    );
    assert_eq!(
        SlabSegmentHdr::get_addr_of_block(x, 1, 1) as usize,
        (x as *const _ as usize) + ALLOC_PAGE_SZ + 8
    );
    assert_eq!(
        SlabSegmentHdr::get_addr_of_block(x, 2, 1) as usize,
        (x as *const _ as usize) + ALLOC_PAGE_SZ * 2 + 8
    );
    assert_eq!(
        SlabSegmentHdr::get_addr_of_block(x, 63, 1) as usize,
        (x as *const _ as usize) + ALLOC_PAGE_SZ * 63 + 8
    );
}

#[cfg(not(loom))]
#[test]
fn slab_basic_single_thread_alloc() {
    let alloc = SlabRoot::<JustU8Mapper>::new();
    let thread_shard = alloc.new_thread();
    let obj_1 = unsafe { thread_shard.allocate::<u8>().0.assume_init_ref() };
    let obj_2 = unsafe { thread_shard.allocate::<u8>().0.assume_init_ref() };
    println!("Allocated obj 1 {:?}", obj_1 as *const _);
    println!("Allocated obj 2 {:?}", obj_2 as *const _);

    assert_eq!(obj_1 as *const _ as usize + 8, obj_2 as *const _ as usize);

    unsafe { thread_shard.free(obj_2) };
    unsafe { thread_shard.free(obj_1) };

    unsafe {
        let seg = thread_shard.per_ty_state[0].segments.get();
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
    let outstanding_blocks = alloc
        .try_lock_global()
        .unwrap()
        ._debug_check_missing_blocks();
    assert_eq!(outstanding_blocks[0].len(), 0);
}

#[cfg(not(loom))]
#[test]
fn slab_basic_fake_remote_free() {
    let alloc = SlabRoot::<JustU8Mapper>::new();
    let thread_shard_0 = alloc.new_thread();
    let obj_1 = unsafe { thread_shard_0.allocate::<u8>().0.assume_init_ref() };
    let obj_2 = unsafe { thread_shard_0.allocate::<u8>().0.assume_init_ref() };
    println!("Allocated obj 1 {:?}", obj_1 as *const _);
    println!("Allocated obj 2 {:?}", obj_2 as *const _);

    let thread_shard_1 = alloc.new_thread();
    unsafe { thread_shard_1.free(obj_2) };
    unsafe { thread_shard_1.free(obj_1) };

    unsafe {
        let seg = thread_shard_0.per_ty_state[0].segments.get();
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
    let outstanding_blocks = alloc
        .try_lock_global()
        .unwrap()
        ._debug_check_missing_blocks();
    assert_eq!(outstanding_blocks[0].len(), 0);
}

#[cfg(not(loom))]
#[test]
fn slab_test_collect_local() {
    let alloc = SlabRoot::<JustBigArrayMapper>::new();
    let thread_shard = alloc.new_thread();
    let obj_1 = unsafe { thread_shard.allocate::<[u8; 30000]>().0.assume_init_ref() };
    let obj_2 = unsafe { thread_shard.allocate::<[u8; 30000]>().0.assume_init_ref() };
    println!("Allocated obj 1 {:?}", obj_1 as *const _);
    println!("Allocated obj 2 {:?}", obj_2 as *const _);

    unsafe { thread_shard.free(obj_1) };
    unsafe { thread_shard.free(obj_2) };

    let obj_1_2nd_try = unsafe { thread_shard.allocate::<[u8; 30000]>().0.assume_init_ref() };
    let obj_2_2nd_try = unsafe { thread_shard.allocate::<[u8; 30000]>().0.assume_init_ref() };
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
    let mut outstanding_blocks = alloc
        .try_lock_global()
        .unwrap()
        ._debug_check_missing_blocks();
    assert!(outstanding_blocks[0].remove(&(obj_1_2nd_try as *const _ as usize)));
    assert!(outstanding_blocks[0].remove(&(obj_2_2nd_try as *const _ as usize)));
    assert_eq!(outstanding_blocks[0].len(), 0);
}

#[cfg(not(loom))]
#[test]
fn slab_test_collect_remote() {
    let alloc = SlabRoot::<JustBigArrayMapper>::new();
    let thread_shard_0 = alloc.new_thread();
    let obj_1 = unsafe { thread_shard_0.allocate::<[u8; 30000]>().0.assume_init_ref() };
    let obj_2 = unsafe { thread_shard_0.allocate::<[u8; 30000]>().0.assume_init_ref() };
    println!("Allocated obj 1 {:?}", obj_1 as *const _);
    println!("Allocated obj 2 {:?}", obj_2 as *const _);

    let thread_shard_1 = alloc.new_thread();
    unsafe { thread_shard_1.free(obj_1) };
    unsafe { thread_shard_1.free(obj_2) };

    let obj_1_2nd_try = unsafe { thread_shard_0.allocate::<[u8; 30000]>().0.assume_init_ref() };
    let obj_2_2nd_try = unsafe { thread_shard_0.allocate::<[u8; 30000]>().0.assume_init_ref() };
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
    let mut outstanding_blocks = alloc
        .try_lock_global()
        .unwrap()
        ._debug_check_missing_blocks();
    assert!(outstanding_blocks[0].remove(&(obj_1_2nd_try as *const _ as usize)));
    assert!(outstanding_blocks[0].remove(&(obj_2_2nd_try as *const _ as usize)));
    assert_eq!(outstanding_blocks[0].len(), 0);
}

#[cfg(not(loom))]
#[test]
fn slab_test_collect_both() {
    let alloc = SlabRoot::<JustBigArrayMapper>::new();
    let thread_shard_0 = alloc.new_thread();
    let obj_1 = unsafe { thread_shard_0.allocate::<[u8; 30000]>().0.assume_init_ref() };
    let obj_2 = unsafe { thread_shard_0.allocate::<[u8; 30000]>().0.assume_init_ref() };
    println!("Allocated obj 1 {:?}", obj_1 as *const _);
    println!("Allocated obj 2 {:?}", obj_2 as *const _);

    let thread_shard_1 = alloc.new_thread();
    unsafe { thread_shard_0.free(obj_1) };
    unsafe { thread_shard_1.free(obj_2) };

    let obj_1_2nd_try = unsafe { thread_shard_0.allocate::<[u8; 30000]>().0.assume_init_ref() };
    let obj_2_2nd_try = unsafe { thread_shard_0.allocate::<[u8; 30000]>().0.assume_init_ref() };
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
    let mut outstanding_blocks = alloc
        .try_lock_global()
        .unwrap()
        ._debug_check_missing_blocks();
    assert!(outstanding_blocks[0].remove(&(obj_1_2nd_try as *const _ as usize)));
    assert!(outstanding_blocks[0].remove(&(obj_2_2nd_try as *const _ as usize)));
    assert_eq!(outstanding_blocks[0].len(), 0);
}

#[cfg(not(loom))]
#[test]
fn slab_test_new_seg() {
    let alloc = SlabRoot::<JustBigArrayMapper>::new();
    let thread_shard = alloc.new_thread();
    let mut things = Vec::new();
    for i in 0..129 {
        let obj = unsafe { thread_shard.allocate::<[u8; 30000]>().0.assume_init_ref() };
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
        let obj = unsafe { thread_shard.allocate::<[u8; 30000]>().0.assume_init_ref() };
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
    let mut outstanding_blocks = alloc
        .try_lock_global()
        .unwrap()
        ._debug_check_missing_blocks();
    for x in things2 {
        assert!(outstanding_blocks[0].remove(&(x as *const _ as usize)));
    }
    assert_eq!(outstanding_blocks[0].len(), 0);
}

#[cfg(not(loom))]
#[test]
fn slab_test_remote_free() {
    let alloc = SlabRoot::<JustBigArrayMapper>::new();
    let thread_shard_0 = alloc.new_thread();
    let thread_shard_1 = alloc.new_thread();
    let mut things = Vec::new();
    for i in 0..129 {
        let obj = unsafe { thread_shard_0.allocate::<[u8; 30000]>().0.assume_init_ref() };
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
        let seg1 = thread_shard_0.per_ty_state[0].segments.get();
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

    let mut test_thread_delayed_item = thread_shard_0.per_ty_state[0]
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

    let mut things2: Vec<&[u8; 30000]> = Vec::new();
    for i in 0..256 {
        let obj = unsafe { thread_shard_0.allocate::<[u8; 30000]>().0.assume_init_ref() };
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
    let mut outstanding_blocks = alloc
        .try_lock_global()
        .unwrap()
        ._debug_check_missing_blocks();
    for x in things2 {
        assert!(outstanding_blocks[0].remove(&(x as *const _ as usize)));
    }
    assert_eq!(outstanding_blocks[0].len(), 0);
}

#[cfg(loom)]
#[test]
fn slab_loom_new_thread() {
    loom::model(|| {
        let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustBigArrayMapper>::new()));

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
        let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustBigArrayMapper>::new()));
        let (sender, receiver) = loom::sync::mpsc::channel();

        let n_objs = 4;

        let t0 = loom::thread::spawn(move || {
            let thread_shard_0 = alloc.new_thread();
            let mut alloc_history = Vec::new();
            let mut prev = None;
            for i in 0..n_objs {
                let obj = thread_shard_0.allocate::<[u8; 30000]>().0;
                let obj_addr = obj.as_ptr() as usize;
                alloc_history.push(obj_addr);
                unsafe {
                    let obj_ = obj.as_ptr() as *mut [u8; 30000];
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
                    obj_addr >= thread_shard_0.per_ty_state[0].segments.get() as *const _ as usize
                );
                assert!(
                    obj_addr
                        < thread_shard_0.per_ty_state[0].segments.get() as *const _ as usize
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
                    let obj_ = obj.as_ptr() as *const u64;
                    assert_eq!(*obj_, (i << 32) | 0xdeadbeef);
                    thread_shard_1.free(obj.assume_init_ref())
                }
            }
        });

        t0.join().unwrap();
        t1.join().unwrap();
    })
}

#[cfg(not(loom))]
#[test]
fn slab_not_loom_smoke_test() {
    let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustBigArrayMapper>::new()));
    let (sender, receiver) = std::sync::mpsc::channel();

    let n_objs = 10_000_000;

    let t0 = std::thread::spawn(move || {
        let thread_shard_0 = alloc.new_thread();
        let mut alloc_history = Vec::new();
        let mut prev = None;
        for i in 0..n_objs {
            let obj = thread_shard_0.allocate::<[u8; 30000]>().0;
            let obj_addr = obj as *const _ as usize;
            unsafe {
                let obj_ = obj.as_ptr() as *mut [u8; 30000];
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
            let mut seg = thread_shard_0.per_ty_state[0].segments.get();
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
                let obj_ = obj.as_ptr() as *const u64;
                assert_eq!(*obj_, (i << 32) | 0xdeadbeef);
                thread_shard_1.free(obj.assume_init_ref())
            }
        }
    });

    t0.join().unwrap();
    t1.join().unwrap();

    let outstanding_blocks = alloc
        .try_lock_global()
        .unwrap()
        ._debug_check_missing_blocks();
    assert_eq!(outstanding_blocks[0].len(), 0);
}

#[cfg(not(loom))]
#[test]
fn slab_global_lock_test() {
    let alloc = SlabRoot::<JustU8Mapper>::new();
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
    let alloc = SlabRoot::<JustU8Mapper>::new();
    let _global = alloc.try_lock_global().unwrap();

    let _thread_shard = alloc.new_thread();
}

#[cfg(not(loom))]
#[test]
fn slab_separate_cells_wires_smoke_test() {
    let alloc = SlabRoot::<TwoBigArrayMapper>::new();
    let thread_shard = alloc.new_thread();

    let cell_obj = unsafe { thread_shard.allocate::<[u8; 30000]>().0.assume_init_ref() };
    let wire_obj = unsafe { thread_shard.allocate::<[u8; 29999]>().0.assume_init_ref() };
    println!("Allocated cell obj {:?}", cell_obj as *const _);
    println!("Allocated wire obj {:?}", wire_obj as *const _);

    // in range
    let cell_obj_addr = cell_obj as *const _ as usize;
    assert!(cell_obj_addr >= thread_shard.per_ty_state[0].segments.get() as *const _ as usize);
    assert!(
        cell_obj_addr
            < thread_shard.per_ty_state[0].segments.get() as *const _ as usize + SEGMENT_SZ
    );
    let wire_obj_addr = wire_obj as *const _ as usize;
    assert!(wire_obj_addr >= thread_shard.per_ty_state[1].segments.get() as *const _ as usize);
    assert!(
        wire_obj_addr
            < thread_shard.per_ty_state[1].segments.get() as *const _ as usize + SEGMENT_SZ
    );

    drop(thread_shard);
    let outstanding_blocks = alloc
        .try_lock_global()
        .unwrap()
        ._debug_check_missing_blocks();
    assert_eq!(outstanding_blocks[0].len(), 1);
    assert_eq!(outstanding_blocks[1].len(), 1);
    assert!(outstanding_blocks[0].contains(&cell_obj_addr));
    assert!(outstanding_blocks[1].contains(&wire_obj_addr));

    // now do a free
    let thread_shard = alloc.new_thread();
    unsafe {
        thread_shard.free(cell_obj);
        thread_shard.free(wire_obj);
    }
    println!("Did a free!");
    drop(thread_shard);
    let outstanding_blocks = alloc
        .try_lock_global()
        .unwrap()
        ._debug_check_missing_blocks();
    assert_eq!(outstanding_blocks[0].len(), 0);
    assert_eq!(outstanding_blocks[1].len(), 0);
}

#[test]
#[ignore = "not automated, human eye verified"]
fn slab_debug_tests() {
    let alloc = SlabRoot::<JustU8Mapper>::new();
    println!("Alloc debug:");
    dbg!(&alloc);

    let thread = alloc.new_thread();
    println!("Thread debug:");
    dbg!(&alloc);
    dbg!(&thread);

    println!("Segment debug:");
    dbg!(&thread.0.per_ty_state[0].segments.get());

    println!("dropping...");
    drop(thread);
    dbg!(&alloc);

    let global = alloc.try_lock_global().unwrap();
    println!("Global debug:");
    dbg!(&global);
    dbg!(&alloc);
}
