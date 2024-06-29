use std::mem::{self, size_of};

use super::*;

#[derive(Default, Debug)]
struct StroadTestingPayload {
    unparked: AtomicBool,
    cancelled: AtomicBool,
}
impl StroadToWorkItemLink for StroadTestingPayload {
    fn unpark(&self, _: &mut ()) {
        self.unparked.store(true, Ordering::Relaxed);
    }

    fn cancel(&self) {
        self.cancelled.store(true, Ordering::Relaxed);
    }

    type UnparkXtraTy = ();
}

#[cfg(not(loom))]
#[test]
fn stroad_lock_held_during_validation() {
    let mut list_ent = StroadNode::<u32, StroadTestingPayload>::default();
    let stroad = Stroad::<u32, StroadTestingPayload>::new();
    let hash = hash(&12345);
    let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
    let _ = stroad.unordered_park_conditionally(&mut list_ent, 12345, || unsafe {
        println!("validation callback");
        let ptr = (*stroad.shards[shard as usize].get())
            .buckets_and_lock
            .load(Ordering::Relaxed);

        assert!(ptr & 1 != 0);

        true
    });
    unsafe {
        let ptr = (*stroad.shards[shard as usize].get())
            .buckets_and_lock
            .load(Ordering::Relaxed);

        assert!(ptr & 1 == 0);
    }
}

#[test]
#[ignore = "not automated, human eye verified"]
fn stroad_manual_tests() {
    println!(
        "size {}",
        mem::size_of::<Stroad<u32, StroadTestingPayload>>()
    );
    let list_ent_0 = StroadNode::<u32, StroadTestingPayload>::default();
    dbg!(&list_ent_0);
    dbg!(size_of::<StroadNode<u32, StroadTestingPayload>>());
    dbg!(size_of::<StroadShard<u32, StroadTestingPayload>>());
    let x = UnsafeCell::new(list_ent_0);
    let x = StroadBucket::<u32, StroadTestingPayload> {
        wants_lock: DoubleLL {
            next: Some(&x),
            prev: Some(&x),
        },
        holds_lock: DoubleLL {
            next: None,
            prev: None,
        },
    };
    dbg!(&x);
    let x = Stroad::<u32, StroadTestingPayload>::new();
    let mut list_ent_0 = StroadNode::<u32, StroadTestingPayload>::default();
    let mut list_ent_1 = StroadNode::<u32, StroadTestingPayload>::default();
    let mut list_ent_2 = StroadNode::<u32, StroadTestingPayload>::default();
    let _ = x.unordered_park_conditionally(&mut list_ent_0, 12345, || true);
    let _ = x.unordered_park_conditionally(&mut list_ent_1, 12345, || true);
    let _ = x.unordered_park_conditionally(&mut list_ent_2, 67890, || true);
    dbg!(&x);
    dbg!(x.lock_shard(19245));
    dbg!(x.lock_shard(19994));
}

#[cfg(not(loom))]
#[test]
fn stroad_park_one() {
    let mut list_ent_0 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<u32, StroadTestingPayload>;
    let stroad = Stroad::<u32, StroadTestingPayload>::new();

    let hash = hash(&12345);
    let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
    let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;

    let _ = stroad.unordered_park_conditionally(&mut list_ent_0, 12345, || true);

    unsafe {
        let shard_data = &*stroad.shards[shard as usize].get();
        assert_eq!(shard_data.capacity_shift, BUCKETS_INITIAL_ENT_SHIFT);
        assert_eq!(shard_data.nents, 1);
        let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
        assert_ne!(ptr, 0);
        let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
        let ptr_i = &*(ptr.add(bucket as usize));
        assert_eq!(
            ptr_i.wants_lock.next.unwrap().get() as *const _,
            list_ent_0_ptr
        );
        assert_eq!(
            ptr_i.wants_lock.prev.unwrap().get() as *const _,
            list_ent_0_ptr
        );

        assert!((*list_ent_0_ptr).link.next.is_none());
        assert!((*list_ent_0_ptr).link.prev.is_none());
        assert_eq!((*list_ent_0_ptr).key.unwrap(), 12345);
    }
}

#[cfg(not(loom))]
#[test]
fn stroad_unpark_all() {
    let mut list_ent_0 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_1 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<u32, StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    let stroad = Stroad::<u32, StroadTestingPayload>::new();

    let _ = stroad.unordered_park_conditionally(&mut list_ent_0, 12345, || true);
    let _ = stroad.unordered_park_conditionally(&mut list_ent_1, 12345, || true);
    stroad.unordered_unpark_all(&12345, &mut ());

    unsafe {
        assert!((*list_ent_0_ptr)
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
        assert!((*list_ent_1_ptr)
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
    }

    let hash = hash(&12345);
    let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
    let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;
    unsafe {
        let shard_data = &*stroad.shards[shard as usize].get();
        assert_eq!(shard_data.capacity_shift, 2);
        assert_eq!(shard_data.nents, 0);
        let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
        assert_ne!(ptr, 0);
        let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
        let ptr_i = &*(ptr.add(bucket as usize));
        assert!(ptr_i.wants_lock.next.is_none());
        assert!(ptr_i.wants_lock.prev.is_none());
    }
}

#[cfg(not(loom))]
#[test]
fn stroad_park_two_separate_buckets() {
    let mut list_ent_0 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_1 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<u32, StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    let stroad = Stroad::<u32, StroadTestingPayload>::new();
    let _ = stroad.unordered_park_conditionally(&mut list_ent_0, 12345, || true);
    let _ = stroad.unordered_park_conditionally(&mut list_ent_1, 67890, || true);

    {
        let hash = hash(&12345);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, BUCKETS_INITIAL_ENT_SHIFT);
            assert_eq!(shard_data.nents, 1);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);
            let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
            let ptr_i = &*(ptr.add(bucket as usize));
            assert_eq!(
                ptr_i.wants_lock.next.unwrap().get() as *const _,
                list_ent_0_ptr
            );
            assert_eq!(
                ptr_i.wants_lock.prev.unwrap().get() as *const _,
                list_ent_0_ptr
            );

            assert!((*list_ent_0_ptr).link.next.is_none());
            assert!((*list_ent_0_ptr).link.prev.is_none());
            assert_eq!((*list_ent_0_ptr).key.unwrap(), 12345);
        }
    }
    {
        let hash = hash(&67890);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, BUCKETS_INITIAL_ENT_SHIFT);
            assert_eq!(shard_data.nents, 1);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);
            let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
            let ptr_i = &*(ptr.add(bucket as usize));
            assert_eq!(
                ptr_i.wants_lock.next.unwrap().get() as *const _,
                list_ent_1_ptr
            );
            assert_eq!(
                ptr_i.wants_lock.prev.unwrap().get() as *const _,
                list_ent_1_ptr
            );

            assert!((*list_ent_1_ptr).link.next.is_none());
            assert!((*list_ent_1_ptr).link.prev.is_none());
            assert_eq!((*list_ent_1_ptr).key.unwrap(), 67890);
        }
    }
}

#[cfg(not(loom))]
#[test]
fn stroad_park_many_same() {
    let mut list_ent_0 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_1 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_2 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_2_ptr = &list_ent_2 as *const StroadNode<u32, StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    dbg!(list_ent_2_ptr);
    let stroad = Stroad::<u32, StroadTestingPayload>::new();

    let _ = stroad.unordered_park_conditionally(&mut list_ent_0, 12345, || true);
    let _ = stroad.unordered_park_conditionally(&mut list_ent_1, 12345, || true);

    {
        let hash = hash(&12345);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 0b11;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, 2);
            assert_eq!(shard_data.nents, 2);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);

            let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
            let ptr_i = &*(ptr.add(bucket as usize));
            assert_eq!(
                ptr_i.wants_lock.next.unwrap().get() as *const _,
                list_ent_1_ptr
            );
            assert_eq!(
                ptr_i.wants_lock.prev.unwrap().get() as *const _,
                list_ent_0_ptr
            );

            assert_eq!(
                (*list_ent_1_ptr).link.next.unwrap().get() as *const _,
                list_ent_0_ptr
            );
            assert!((*list_ent_1_ptr).link.prev.is_none());

            assert!((*list_ent_0_ptr).link.next.is_none());
            assert_eq!(
                (*list_ent_0_ptr).link.prev.unwrap().get() as *const _,
                list_ent_1_ptr
            );
        }
    }

    let _ = stroad.unordered_park_conditionally(&mut list_ent_2, 12345, || true);

    {
        let hash = hash(&12345);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 0b111;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, 3);
            assert_eq!(shard_data.nents, 3);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);

            let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
            let ptr_i = &*(ptr.add(bucket as usize));
            assert_eq!(
                ptr_i.wants_lock.next.unwrap().get() as *const _,
                list_ent_2_ptr
            );
            assert_eq!(
                ptr_i.wants_lock.prev.unwrap().get() as *const _,
                list_ent_0_ptr
            );

            assert_eq!(
                (*list_ent_2_ptr).link.next.unwrap().get() as *const _,
                list_ent_1_ptr
            );
            assert!((*list_ent_2_ptr).link.prev.is_none());

            assert_eq!(
                (*list_ent_1_ptr).link.next.unwrap().get() as *const _,
                list_ent_0_ptr
            );
            assert_eq!(
                (*list_ent_1_ptr).link.prev.unwrap().get() as *const _,
                list_ent_2_ptr
            );

            assert!((*list_ent_0_ptr).link.next.is_none());
            assert_eq!(
                (*list_ent_0_ptr).link.prev.unwrap().get() as *const _,
                list_ent_1_ptr
            );
        }
    }
}

#[cfg(not(loom))]
#[test]
fn stroad_priority_locking() {
    let mut list_ent_0 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_1 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_2 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_2_ptr = &list_ent_2 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_3 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_3_ptr = &list_ent_3 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_4 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_4_ptr = &list_ent_4 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_5 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_5_ptr = &list_ent_5 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_6 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_6_ptr = &list_ent_6 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_7 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_7_ptr = &list_ent_7 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_8 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_8_ptr = &list_ent_8 as *const StroadNode<u32, StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    dbg!(list_ent_2_ptr);
    dbg!(list_ent_3_ptr);
    dbg!(list_ent_4_ptr);
    dbg!(list_ent_5_ptr);
    dbg!(list_ent_6_ptr);
    dbg!(list_ent_7_ptr);
    dbg!(list_ent_8_ptr);
    let stroad = Stroad::<u32, StroadTestingPayload>::new();

    // some readers
    println!("* ent 0");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_0, 12345, 0, || {});
    assert!(ret);
    println!("* ent 1");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_1, 12345, 1, || {});
    assert!(ret);

    // failed writers
    println!("* ent 2");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_2, 12345, -2, || {});
    assert!(!ret);
    println!("* ent 3");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_3, 12345, -1, || {});
    assert!(!ret);

    // success writer
    println!("* ent 4");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_4, 12345, -10, || {});
    assert!(ret);

    // fail writer
    println!("* ent 5");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_5, 12345, -11, || {});
    assert!(!ret);
    // success writer, cancel _ent_4
    println!("* ent 6");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_6, 12345, -9, || {});
    assert!(ret);
    unsafe {
        assert!((*list_ent_4_ptr)
            .work_item_link
            .cancelled
            .load(Ordering::Relaxed));
    }

    // fail reader
    println!("* ent 7");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_7, 12345, 8, || {});
    assert!(!ret);
    // success reader
    println!("* ent 8");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_8, 12345, 7, || {});
    assert!(ret);

    // test the lists
    {
        let hash = hash(&12345);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 0b111;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, 4);
            assert_eq!(shard_data.nents, 8);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);

            let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
            let ptr_i = &*(ptr.add(bucket as usize));

            // holds lock list
            assert_eq!(
                ptr_i.holds_lock.next.unwrap().get() as *const _,
                list_ent_8_ptr
            );
            assert_eq!(
                ptr_i.holds_lock.prev.unwrap().get() as *const _,
                list_ent_0_ptr
            );

            assert_eq!(
                (*list_ent_8_ptr).link.next.unwrap().get() as *const _,
                list_ent_6_ptr
            );
            assert!((*list_ent_8_ptr).link.prev.is_none());

            assert_eq!(
                (*list_ent_6_ptr).link.next.unwrap().get() as *const _,
                list_ent_1_ptr
            );
            assert_eq!(
                (*list_ent_6_ptr).link.prev.unwrap().get() as *const _,
                list_ent_8_ptr
            );

            assert_eq!(
                (*list_ent_1_ptr).link.next.unwrap().get() as *const _,
                list_ent_0_ptr
            );
            assert_eq!(
                (*list_ent_1_ptr).link.prev.unwrap().get() as *const _,
                list_ent_6_ptr
            );

            assert!((*list_ent_0_ptr).link.next.is_none());
            assert_eq!(
                (*list_ent_0_ptr).link.prev.unwrap().get() as *const _,
                list_ent_1_ptr
            );

            // wants lock list
            assert_eq!(
                ptr_i.wants_lock.next.unwrap().get() as *const _,
                list_ent_7_ptr
            );
            assert_eq!(
                ptr_i.wants_lock.prev.unwrap().get() as *const _,
                list_ent_2_ptr
            );

            assert_eq!(
                (*list_ent_7_ptr).link.next.unwrap().get() as *const _,
                list_ent_5_ptr
            );
            assert!((*list_ent_7_ptr).link.prev.is_none());

            assert_eq!(
                (*list_ent_5_ptr).link.next.unwrap().get() as *const _,
                list_ent_3_ptr
            );
            assert_eq!(
                (*list_ent_5_ptr).link.prev.unwrap().get() as *const _,
                list_ent_7_ptr
            );

            assert_eq!(
                (*list_ent_3_ptr).link.next.unwrap().get() as *const _,
                list_ent_2_ptr
            );
            assert_eq!(
                (*list_ent_3_ptr).link.prev.unwrap().get() as *const _,
                list_ent_5_ptr
            );

            assert!((*list_ent_2_ptr).link.next.is_none());
            assert_eq!(
                (*list_ent_2_ptr).link.prev.unwrap().get() as *const _,
                list_ent_3_ptr
            );
        }
    }
}

#[cfg(not(loom))]
#[test]
fn stroad_writer_canceling_readers() {
    let mut list_ent_0 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_1 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_2 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_2_ptr = &list_ent_2 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_3 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_3_ptr = &list_ent_3 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_4 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_4_ptr = &list_ent_4 as *const StroadNode<u32, StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    dbg!(list_ent_2_ptr);
    dbg!(list_ent_3_ptr);
    dbg!(list_ent_4_ptr);
    let stroad = Stroad::<u32, StroadTestingPayload>::new();

    // some readers, spaced out
    println!("* ent 0");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_0, 12345, 1, || {});
    assert!(ret);
    println!("* ent 1");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_1, 12345, 3, || {});
    assert!(ret);
    println!("* ent 2");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_2, 12345, 5, || {});
    assert!(ret);
    println!("* ent 3");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_3, 12345, 7, || {});
    assert!(ret);

    // success writer, cancel _ent_2 and _ent 3
    println!("* ent 4");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_4, 12345, -5, || {});
    assert!(ret);
    unsafe {
        assert!((*list_ent_3_ptr)
            .work_item_link
            .cancelled
            .load(Ordering::Relaxed));
        assert!((*list_ent_2_ptr)
            .work_item_link
            .cancelled
            .load(Ordering::Relaxed));
    }

    // test the lists
    {
        let hash = hash(&12345);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 0b111;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, 3);
            assert_eq!(shard_data.nents, 3);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);

            let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
            let ptr_i = &*(ptr.add(bucket as usize));

            // holds lock list
            assert_eq!(
                ptr_i.holds_lock.next.unwrap().get() as *const _,
                list_ent_4_ptr
            );
            assert_eq!(
                ptr_i.holds_lock.prev.unwrap().get() as *const _,
                list_ent_0_ptr
            );

            assert_eq!(
                (*list_ent_4_ptr).link.next.unwrap().get() as *const _,
                list_ent_1_ptr
            );
            assert!((*list_ent_4_ptr).link.prev.is_none());

            assert_eq!(
                (*list_ent_1_ptr).link.next.unwrap().get() as *const _,
                list_ent_0_ptr
            );
            assert_eq!(
                (*list_ent_1_ptr).link.prev.unwrap().get() as *const _,
                list_ent_4_ptr
            );

            assert!((*list_ent_0_ptr).link.next.is_none());
            assert_eq!(
                (*list_ent_0_ptr).link.prev.unwrap().get() as *const _,
                list_ent_1_ptr
            );

            // wants lock list
            assert!(ptr_i.wants_lock.next.is_none());
            assert!(ptr_i.wants_lock.prev.is_none());
        }
    }
}

#[cfg(not(loom))]
#[test]
fn stroad_priority_unlocking() {
    let mut list_ent_0 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_1 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_2 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_2_ptr = &list_ent_2 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_3 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_3_ptr = &list_ent_3 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_4 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_4_ptr = &list_ent_4 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_5 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_5_ptr = &list_ent_5 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_6 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_6_ptr = &list_ent_6 as *const StroadNode<u32, StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    dbg!(list_ent_2_ptr);
    dbg!(list_ent_3_ptr);
    dbg!(list_ent_4_ptr);
    dbg!(list_ent_5_ptr);
    dbg!(list_ent_6_ptr);
    let stroad = Stroad::<u32, StroadTestingPayload>::new();

    println!("* ent 0");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_0, 12345, 0, || {});
    assert!(ret);
    println!("* ent 1");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_1, 12345, 1, || {});
    assert!(ret);
    println!("* ent 2");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_2, 12345, -3, || {});
    assert!(ret);
    println!("* ent 3");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_3, 12345, 3, || {});
    assert!(!ret);
    println!("* ent 4");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_4, 12345, 4, || {});
    assert!(!ret);
    println!("* ent 5");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_5, 12345, -5, || {});
    assert!(!ret);
    println!("* ent 6");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_6, 12345, -5, || {});
    assert!(!ret);

    // ent 2 will cause an unlock (as a writer)
    println!("** unlock ent 2");
    stroad.ordered_do_unlocking(unsafe { &*(list_ent_2_ptr) }, || true, || {}, &mut ());
    unsafe {
        assert!((*list_ent_4_ptr)
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
        assert!((*list_ent_3_ptr)
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
    }

    // *one* of the readers will cause an unlock
    // it *shouldn't* matter which, as long as it's the last
    println!("** unlock ent 3");
    stroad.ordered_do_unlocking(unsafe { &*(list_ent_3_ptr) }, || true, || {}, &mut ());
    unsafe {
        assert!((*list_ent_6_ptr)
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
    }

    // this should unlock the other writer
    println!("** unlock ent 6");
    stroad.ordered_do_unlocking(unsafe { &*(list_ent_6_ptr) }, || true, || {}, &mut ());
    unsafe {
        assert!((*list_ent_5_ptr)
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
    }

    // this should unlock nothing
    println!("** unlock ent 5");
    stroad.ordered_do_unlocking(unsafe { &*(list_ent_5_ptr) }, || true, || {}, &mut ());
}

#[cfg(not(loom))]
#[test]
fn stroad_writers_dont_cancel_if_conflict() {
    let mut list_ent_0 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_1 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<u32, StroadTestingPayload>;
    let mut list_ent_2 = StroadNode::<u32, StroadTestingPayload>::default();
    let list_ent_2_ptr = &list_ent_2 as *const StroadNode<u32, StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    dbg!(list_ent_2_ptr);
    let stroad = Stroad::<u32, StroadTestingPayload>::new();

    println!("* ent 0");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_0, 12345, 0, || {});
    assert!(ret);
    println!("* ent 1");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_1, 12345, -2, || {});
    assert!(ret);
    println!("* ent 2");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_2, 12345, -1, || {});
    assert!(!ret); // won't work, conflicts with the reader

    unsafe {
        assert!(!(*list_ent_0_ptr)
            .work_item_link
            .cancelled
            .load(Ordering::Relaxed));
        assert!(!(*list_ent_1_ptr)
            .work_item_link
            .cancelled
            .load(Ordering::Relaxed));
    }
}

#[test]
#[cfg(loom)]
fn stroad_loom_concurrent_park() {
    loom::model(|| {
        let list_ent_0 = Box::leak(Box::new(StroadNode::<u32, StroadTestingPayload>::default()));
        let list_ent_0_ptr = list_ent_0 as *const StroadNode<u32, StroadTestingPayload>;
        let list_ent_1 = Box::leak(Box::new(StroadNode::<u32, StroadTestingPayload>::default()));
        let list_ent_1_ptr = list_ent_1 as *const StroadNode<u32, StroadTestingPayload>;
        let stroad = &*Box::leak(Stroad::<u32, StroadTestingPayload>::new());

        let t1 = loom::thread::spawn(move || {
            let _ = stroad.unordered_park_conditionally(list_ent_0, 12345, || true);
        });
        let t2 = loom::thread::spawn(move || {
            let _ = stroad.unordered_park_conditionally(list_ent_1, 12345, || true);
        });
        t1.join().unwrap();
        t2.join().unwrap();

        {
            let hash = hash(&12345);
            let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
            let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;

            unsafe {
                let shard_data = &*stroad.shards[shard as usize].get();
                assert_eq!(shard_data.capacity_shift, 2);
                assert_eq!(shard_data.nents, 2);
                let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
                assert_ne!(ptr, 0);
                let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
                let ptr_i = &*(ptr.add(bucket as usize));

                if ptr_i.wants_lock.next.unwrap().get() as *const _ == list_ent_0_ptr {
                    assert_eq!(
                        ptr_i.wants_lock.next.unwrap().get() as *const _,
                        list_ent_0_ptr
                    );
                    assert_eq!(
                        ptr_i.wants_lock.prev.unwrap().get() as *const _,
                        list_ent_1_ptr
                    );

                    assert_eq!(
                        (*list_ent_0_ptr).link.next.unwrap().get() as *const _,
                        list_ent_1_ptr
                    );
                    assert!((*list_ent_0_ptr).link.prev.is_none());
                    assert_eq!((*list_ent_0_ptr).key.unwrap(), 12345);

                    assert!((*list_ent_1_ptr).link.next.is_none());
                    assert_eq!(
                        (*list_ent_1_ptr).link.prev.unwrap().get() as *const _,
                        list_ent_0_ptr
                    );
                    assert_eq!((*list_ent_1_ptr).key.unwrap(), 12345);
                } else if ptr_i.wants_lock.next.unwrap().get() as *const _ == list_ent_1_ptr {
                    assert_eq!(
                        ptr_i.wants_lock.next.unwrap().get() as *const _,
                        list_ent_1_ptr
                    );
                    assert_eq!(
                        ptr_i.wants_lock.prev.unwrap().get() as *const _,
                        list_ent_0_ptr
                    );

                    assert_eq!(
                        (*list_ent_1_ptr).link.next.unwrap().get() as *const _,
                        list_ent_0_ptr
                    );
                    assert!((*list_ent_1_ptr).link.prev.is_none());
                    assert_eq!((*list_ent_1_ptr).key.unwrap(), 12345);

                    assert!((*list_ent_0_ptr).link.next.is_none());
                    assert_eq!(
                        (*list_ent_0_ptr).link.prev.unwrap().get() as *const _,
                        list_ent_1_ptr
                    );
                    assert_eq!((*list_ent_0_ptr).key.unwrap(), 12345);
                } else {
                    panic!("bad list pointer");
                }
            }
        }
    })
}

#[test]
#[cfg(loom)]
fn stroad_loom_park_unpark() {
    loom::model(|| {
        let list_ent_0 = Box::leak(Box::new(StroadNode::<u32, StroadTestingPayload>::default()));
        let list_ent_0_ptr = list_ent_0 as *const StroadNode<u32, StroadTestingPayload>;
        let list_ent_1 = Box::leak(Box::new(StroadNode::<u32, StroadTestingPayload>::default()));
        let list_ent_1_ptr = list_ent_1 as *const StroadNode<u32, StroadTestingPayload>;
        let stroad = &*Box::leak(Stroad::<u32, StroadTestingPayload>::new());
        let _ = stroad.unordered_park_conditionally(list_ent_0, 12345, || true);

        let t1 = loom::thread::spawn(move || {
            let _ = stroad.unordered_park_conditionally(list_ent_1, 12345, || true);
        });
        let t2 = loom::thread::spawn(move || {
            stroad.unordered_unpark_all(&12345, &mut ());
        });
        t1.join().unwrap();
        t2.join().unwrap();

        {
            let ent_0_unparked = unsafe {
                (*list_ent_0_ptr)
                    .work_item_link
                    .unparked
                    .load(Ordering::Relaxed)
            };
            let ent_1_unparked = unsafe {
                (*list_ent_1_ptr)
                    .work_item_link
                    .unparked
                    .load(Ordering::Relaxed)
            };
            assert!(ent_0_unparked || ent_1_unparked);
            if !ent_1_unparked {
                let hash = hash(&12345);
                let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
                let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;

                unsafe {
                    let shard_data = &*stroad.shards[shard as usize].get();
                    assert_eq!(shard_data.nents, 1);
                    let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
                    assert_ne!(ptr, 0);
                    let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
                    let ptr_i = &*(ptr.add(bucket as usize));

                    assert_eq!(
                        ptr_i.wants_lock.next.unwrap().get() as *const _,
                        list_ent_1_ptr
                    );
                    assert_eq!(
                        ptr_i.wants_lock.prev.unwrap().get() as *const _,
                        list_ent_1_ptr
                    );

                    assert!((*list_ent_1_ptr).link.next.is_none());
                    assert!((*list_ent_1_ptr).link.prev.is_none());
                }
            } else {
                let hash = hash(&12345);
                let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
                let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;

                unsafe {
                    let shard_data = &*stroad.shards[shard as usize].get();
                    assert_eq!(shard_data.nents, 0);
                    let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
                    assert_ne!(ptr, 0);
                    let ptr = ptr as *const StroadBucket<u32, StroadTestingPayload>;
                    let ptr_i = &*(ptr.add(bucket as usize));

                    assert!(ptr_i.wants_lock.next.is_none());
                    assert!(ptr_i.wants_lock.prev.is_none());
                }
            }
        }
    })
}
