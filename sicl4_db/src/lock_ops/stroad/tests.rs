use std::mem::{self, size_of, MaybeUninit};

use crate::lock_ops::*;

use super::*;

struct DebugDummyQueue {}
impl WorkQueueInterface for DebugDummyQueue {
    type WorkItemTy = ();
    fn add_work(&mut self, _: Self::WorkItemTy) {}
}

#[derive(Default, Debug)]
struct StroadTestingPayload {
    unparked: AtomicBool,
    cancelled: AtomicBool,
}
impl WorkItemInterface for StroadTestingPayload {
    type WorkItemTy = ();

    fn unpark<Q: WorkQueueInterface<WorkItemTy = Self::WorkItemTy>>(&self, _onto_q: &mut Q) {
        self.unparked.store(true, Ordering::Relaxed);
    }

    fn cancel<Q: WorkQueueInterface<WorkItemTy = Self::WorkItemTy>>(&self, _onto_q: &mut Q) {
        self.cancelled.store(true, Ordering::Relaxed);
    }
}

#[cfg(not(loom))]
static DUMMY_OBJ_0: LockedObj<()> = LockedObj {
    lock_and_generation: AtomicU64::new(LOCK_GEN_VALID_BIT),
    num_rw: UnsafeCell::new(0),
    payload: UnsafeCell::new(()),
};
#[cfg(not(loom))]
static DUMMY_OBJ_0_REF: TypeErasedObjRef = ObjRef {
    ptr: &DUMMY_OBJ_0,
    gen: 0,
}
.type_erase();
#[cfg(not(loom))]
static DUMMY_OBJ_1: LockedObj<()> = LockedObj {
    lock_and_generation: AtomicU64::new(LOCK_GEN_VALID_BIT),
    num_rw: UnsafeCell::new(0),
    payload: UnsafeCell::new(()),
};
#[cfg(not(loom))]
static DUMMY_OBJ_1_REF: TypeErasedObjRef = ObjRef {
    ptr: &DUMMY_OBJ_1,
    gen: 0,
}
.type_erase();

#[cfg(not(loom))]
#[test]
fn stroad_lock_held_during_validation() {
    let mut list_ent = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let stroad = Stroad::<StroadTestingPayload>::new();
    let hash = hash(DUMMY_OBJ_0_REF);
    let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
    let _ = stroad.unordered_park_conditionally(&mut list_ent, || unsafe {
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

#[cfg(not(loom))]
#[test]
#[ignore = "not automated, human eye verified"]
fn stroad_manual_tests() {
    println!("size {}", mem::size_of::<Stroad<StroadTestingPayload>>());
    let list_ent_0 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    dbg!(&list_ent_0);
    dbg!(size_of::<StroadNode<StroadTestingPayload>>());
    dbg!(size_of::<StroadShard<StroadTestingPayload>>());
    let x = UnsafeCell::new(list_ent_0);
    let x = StroadBucket::<StroadTestingPayload> {
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
    let x = Stroad::<StroadTestingPayload>::new();
    let mut list_ent_0 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let mut list_ent_1 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let mut list_ent_2 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_1_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let _ = x.unordered_park_conditionally(&mut list_ent_0, || true);
    let _ = x.unordered_park_conditionally(&mut list_ent_1, || true);
    let _ = x.unordered_park_conditionally(&mut list_ent_2, || true);
    dbg!(&x);
    dbg!(x.lock_shard((hash(DUMMY_OBJ_0_REF) & (HASH_NUM_SHARDS as u64 - 1)) as usize));
    dbg!(x.lock_shard((hash(DUMMY_OBJ_1_REF) & (HASH_NUM_SHARDS as u64 - 1)) as usize));
}

#[cfg(not(loom))]
#[test]
fn stroad_park_one() {
    let mut list_ent_0 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<StroadTestingPayload>;
    let stroad = Stroad::<StroadTestingPayload>::new();

    let hash = hash(DUMMY_OBJ_0_REF);
    let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
    let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;

    let _ = stroad.unordered_park_conditionally(&mut list_ent_0, || true);

    unsafe {
        let shard_data = &*stroad.shards[shard as usize].get();
        assert_eq!(shard_data.capacity_shift, BUCKETS_INITIAL_ENT_SHIFT);
        assert_eq!(shard_data.nents, 1);
        let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
        assert_ne!(ptr, 0);
        let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
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
        assert_eq!((*list_ent_0_ptr).key, DUMMY_OBJ_0_REF);
    }
}

#[cfg(not(loom))]
#[test]
fn stroad_unpark_all() {
    let mut list_ent_0 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_1 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    let stroad = Stroad::<StroadTestingPayload>::new();

    let _ = stroad.unordered_park_conditionally(&mut list_ent_0, || true);
    let _ = stroad.unordered_park_conditionally(&mut list_ent_1, || true);
    stroad.unordered_unpark_all(DUMMY_OBJ_0_REF, &mut DebugDummyQueue {});

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

    let hash = hash(DUMMY_OBJ_0_REF);
    let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
    let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;
    unsafe {
        let shard_data = &*stroad.shards[shard as usize].get();
        assert_eq!(shard_data.capacity_shift, 2);
        assert_eq!(shard_data.nents, 0);
        let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
        assert_ne!(ptr, 0);
        let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
        let ptr_i = &*(ptr.add(bucket as usize));
        assert!(ptr_i.wants_lock.next.is_none());
        assert!(ptr_i.wants_lock.prev.is_none());
    }
}

#[cfg(not(loom))]
#[test]
fn stroad_park_two_separate_buckets() {
    let mut list_ent_0 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_1 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_1_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    let stroad = Stroad::<StroadTestingPayload>::new();
    let _ = stroad.unordered_park_conditionally(&mut list_ent_0, || true);
    let _ = stroad.unordered_park_conditionally(&mut list_ent_1, || true);

    {
        let hash = hash(DUMMY_OBJ_0_REF);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, BUCKETS_INITIAL_ENT_SHIFT);
            assert_eq!(shard_data.nents, 1);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);
            let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
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
            assert_eq!((*list_ent_0_ptr).key, DUMMY_OBJ_0_REF);
        }
    }
    {
        let hash = hash(DUMMY_OBJ_1_REF);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, BUCKETS_INITIAL_ENT_SHIFT);
            assert_eq!(shard_data.nents, 1);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);
            let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
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
            assert_eq!((*list_ent_1_ptr).key, DUMMY_OBJ_1_REF);
        }
    }
}

#[cfg(not(loom))]
#[test]
fn stroad_park_many_same() {
    let mut list_ent_0 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_1 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_2 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_2_ptr = &list_ent_2 as *const StroadNode<StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    dbg!(list_ent_2_ptr);
    let stroad = Stroad::<StroadTestingPayload>::new();

    let _ = stroad.unordered_park_conditionally(&mut list_ent_0, || true);
    let _ = stroad.unordered_park_conditionally(&mut list_ent_1, || true);

    {
        let hash = hash(DUMMY_OBJ_0_REF);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 0b11;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, 2);
            assert_eq!(shard_data.nents, 2);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);

            let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
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

    let _ = stroad.unordered_park_conditionally(&mut list_ent_2, || true);

    {
        let hash = hash(DUMMY_OBJ_0_REF);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 0b111;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, 3);
            assert_eq!(shard_data.nents, 3);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);

            let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
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
    let mut list_ent_0 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_1 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_2 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_2_ptr = &list_ent_2 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_3 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_3_ptr = &list_ent_3 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_4 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_4_ptr = &list_ent_4 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_5 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_5_ptr = &list_ent_5 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_6 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_6_ptr = &list_ent_6 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_7 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_7_ptr = &list_ent_7 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_8 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_8_ptr = &list_ent_8 as *const StroadNode<StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    dbg!(list_ent_2_ptr);
    dbg!(list_ent_3_ptr);
    dbg!(list_ent_4_ptr);
    dbg!(list_ent_5_ptr);
    dbg!(list_ent_6_ptr);
    dbg!(list_ent_7_ptr);
    dbg!(list_ent_8_ptr);
    let stroad = Stroad::<StroadTestingPayload>::new();

    // some readers
    println!("* ent 0");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_0, 0, || {}, &mut DebugDummyQueue {});
    assert!(ret);
    println!("* ent 1");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_1, 1, || {}, &mut DebugDummyQueue {});
    assert!(ret);

    // failed writers
    println!("* ent 2");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_2, -2, || {}, &mut DebugDummyQueue {});
    assert!(!ret);
    println!("* ent 3");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_3, -1, || {}, &mut DebugDummyQueue {});
    assert!(!ret);

    // success writer
    println!("* ent 4");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_4, -10, || {}, &mut DebugDummyQueue {});
    assert!(ret);

    // fail writer
    println!("* ent 5");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_5, -11, || {}, &mut DebugDummyQueue {});
    assert!(!ret);
    // success writer, cancel _ent_4
    println!("* ent 6");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_6, -9, || {}, &mut DebugDummyQueue {});
    assert!(ret);
    unsafe {
        assert!((*list_ent_4_ptr)
            .work_item_link
            .cancelled
            .load(Ordering::Relaxed));
    }

    // fail reader
    println!("* ent 7");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_7, 8, || {}, &mut DebugDummyQueue {});
    assert!(!ret);
    // success reader
    println!("* ent 8");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_8, 7, || {}, &mut DebugDummyQueue {});
    assert!(ret);

    // test the lists
    {
        let hash = hash(DUMMY_OBJ_0_REF);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 0b1111;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, 4);
            assert_eq!(shard_data.nents, 8);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);

            let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
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
    let mut list_ent_0 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_1 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_2 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_2_ptr = &list_ent_2 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_3 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_3_ptr = &list_ent_3 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_4 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_4_ptr = &list_ent_4 as *const StroadNode<StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    dbg!(list_ent_2_ptr);
    dbg!(list_ent_3_ptr);
    dbg!(list_ent_4_ptr);
    let stroad = Stroad::<StroadTestingPayload>::new();

    // some readers, spaced out
    println!("* ent 0");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_0, 1, || {}, &mut DebugDummyQueue {});
    assert!(ret);
    println!("* ent 1");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_1, 3, || {}, &mut DebugDummyQueue {});
    assert!(ret);
    println!("* ent 2");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_2, 5, || {}, &mut DebugDummyQueue {});
    assert!(ret);
    println!("* ent 3");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_3, 7, || {}, &mut DebugDummyQueue {});
    assert!(ret);

    // success writer, cancel _ent_2 and _ent 3
    println!("* ent 4");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_4, -5, || {}, &mut DebugDummyQueue {});
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
        let hash = hash(DUMMY_OBJ_0_REF);
        let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
        let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 0b111;

        unsafe {
            let shard_data = &*stroad.shards[shard as usize].get();
            assert_eq!(shard_data.capacity_shift, 3);
            assert_eq!(shard_data.nents, 3);
            let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
            assert_ne!(ptr, 0);

            let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
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
    let mut list_ent_0 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_1 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_2 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_2_ptr = &list_ent_2 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_3 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_3_ptr = &list_ent_3 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_4 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_4_ptr = &list_ent_4 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_5 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_5_ptr = &list_ent_5 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_6 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_6_ptr = &list_ent_6 as *const StroadNode<StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    dbg!(list_ent_2_ptr);
    dbg!(list_ent_3_ptr);
    dbg!(list_ent_4_ptr);
    dbg!(list_ent_5_ptr);
    dbg!(list_ent_6_ptr);
    let stroad = Stroad::<StroadTestingPayload>::new();

    println!("* ent 0");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_0, 0, || {}, &mut DebugDummyQueue {});
    assert!(ret);
    println!("* ent 1");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_1, 1, || {}, &mut DebugDummyQueue {});
    assert!(ret);
    println!("* ent 2");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_2, -3, || {}, &mut DebugDummyQueue {});
    assert!(ret);
    println!("* ent 3");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_3, 3, || {}, &mut DebugDummyQueue {});
    assert!(!ret);
    println!("* ent 4");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_4, 4, || {}, &mut DebugDummyQueue {});
    assert!(!ret);
    println!("* ent 5");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_5, -5, || {}, &mut DebugDummyQueue {});
    assert!(!ret);
    println!("* ent 6");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_6, -5, || {}, &mut DebugDummyQueue {});
    assert!(!ret);

    // ent 2 will cause an unlock (as a writer)
    println!("** unlock ent 2");
    stroad.ordered_do_unlocking(
        unsafe { &*(list_ent_2_ptr) },
        || true,
        || {},
        &mut DebugDummyQueue {},
    );
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
    stroad.ordered_do_unlocking(
        unsafe { &*(list_ent_3_ptr) },
        || true,
        || {},
        &mut DebugDummyQueue {},
    );
    unsafe {
        assert!((*list_ent_6_ptr)
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
    }

    // this should unlock the other writer
    println!("** unlock ent 6");
    stroad.ordered_do_unlocking(
        unsafe { &*(list_ent_6_ptr) },
        || true,
        || {},
        &mut DebugDummyQueue {},
    );
    unsafe {
        assert!((*list_ent_5_ptr)
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
    }

    // this should unlock nothing
    println!("** unlock ent 5");
    stroad.ordered_do_unlocking(
        unsafe { &*(list_ent_5_ptr) },
        || true,
        || {},
        &mut DebugDummyQueue {},
    );
}

#[cfg(not(loom))]
#[test]
fn stroad_writers_dont_cancel_if_conflict() {
    let mut list_ent_0 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_0_ptr = &list_ent_0 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_1 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_1_ptr = &list_ent_1 as *const StroadNode<StroadTestingPayload>;
    let mut list_ent_2 = {
        let mut x = MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit();
        unsafe {
            StroadNode::init(x.as_mut_ptr(), DUMMY_OBJ_0_REF);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init()
        }
    };
    let list_ent_2_ptr = &list_ent_2 as *const StroadNode<StroadTestingPayload>;
    dbg!(list_ent_0_ptr);
    dbg!(list_ent_1_ptr);
    dbg!(list_ent_2_ptr);
    let stroad = Stroad::<StroadTestingPayload>::new();

    println!("* ent 0");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_0, 0, || {}, &mut DebugDummyQueue {});
    assert!(ret);
    println!("* ent 1");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_1, -2, || {}, &mut DebugDummyQueue {});
    assert!(ret);
    println!("* ent 2");
    let (ret, _) = stroad.ordered_do_locking(&mut list_ent_2, -1, || {}, &mut DebugDummyQueue {});
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
        let loom_dummy_obj = Box::leak(Box::new(LockedObj {
            lock_and_generation: AtomicU64::new(LOCK_GEN_VALID_BIT),
            num_rw: UnsafeCell::new(0),
            payload: UnsafeCell::new(()),
        }));
        let loom_dummy_obj_ref: TypeErasedObjRef = ObjRef {
            ptr: loom_dummy_obj,
            gen: 0,
        }
        .type_erase();

        let list_ent_0 = unsafe {
            let x = Box::leak(Box::new(
                MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit(),
            ));
            StroadNode::init(x.as_mut_ptr(), loom_dummy_obj_ref);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init_mut()
        };
        let list_ent_0_ptr = list_ent_0 as *const StroadNode<StroadTestingPayload>;
        let list_ent_1 = unsafe {
            let x = Box::leak(Box::new(
                MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit(),
            ));
            StroadNode::init(x.as_mut_ptr(), loom_dummy_obj_ref);

            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init_mut()
        };
        let list_ent_1_ptr = list_ent_1 as *const StroadNode<StroadTestingPayload>;
        let stroad = &*Box::leak(Stroad::<StroadTestingPayload>::new());

        let t1 = loom::thread::spawn(move || {
            let _ = stroad.unordered_park_conditionally(list_ent_0, || true);
        });
        let t2 = loom::thread::spawn(move || {
            let _ = stroad.unordered_park_conditionally(list_ent_1, || true);
        });
        t1.join().unwrap();
        t2.join().unwrap();

        {
            let hash = hash(loom_dummy_obj_ref);
            let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
            let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 0b11;

            unsafe {
                let shard_data = &*stroad.shards[shard as usize].get();
                assert_eq!(shard_data.capacity_shift, 2);
                assert_eq!(shard_data.nents, 2);
                let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
                assert_ne!(ptr, 0);
                let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
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
                    assert_eq!((*list_ent_0_ptr).key, loom_dummy_obj_ref);

                    assert!((*list_ent_1_ptr).link.next.is_none());
                    assert_eq!(
                        (*list_ent_1_ptr).link.prev.unwrap().get() as *const _,
                        list_ent_0_ptr
                    );
                    assert_eq!((*list_ent_1_ptr).key, loom_dummy_obj_ref);
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
                    assert_eq!((*list_ent_1_ptr).key, loom_dummy_obj_ref);

                    assert!((*list_ent_0_ptr).link.next.is_none());
                    assert_eq!(
                        (*list_ent_0_ptr).link.prev.unwrap().get() as *const _,
                        list_ent_1_ptr
                    );
                    assert_eq!((*list_ent_0_ptr).key, loom_dummy_obj_ref);
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
        let loom_dummy_obj = Box::leak(Box::new(LockedObj {
            lock_and_generation: AtomicU64::new(LOCK_GEN_VALID_BIT),
            num_rw: UnsafeCell::new(0),
            payload: UnsafeCell::new(()),
        }));
        let loom_dummy_obj_ref: TypeErasedObjRef = ObjRef {
            ptr: loom_dummy_obj,
            gen: 0,
        }
        .type_erase();

        let list_ent_0 = unsafe {
            let x = Box::leak(Box::new(
                MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit(),
            ));
            StroadNode::init(x.as_mut_ptr(), loom_dummy_obj_ref);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init_mut()
        };
        let list_ent_0_ptr = list_ent_0 as *const StroadNode<StroadTestingPayload>;
        let list_ent_1 = unsafe {
            let x = Box::leak(Box::new(
                MaybeUninit::<StroadNode<StroadTestingPayload>>::uninit(),
            ));
            StroadNode::init(x.as_mut_ptr(), loom_dummy_obj_ref);
            (*x.as_mut_ptr()).work_item_link = StroadTestingPayload::default();
            x.assume_init_mut()
        };
        let list_ent_1_ptr = list_ent_1 as *const StroadNode<StroadTestingPayload>;
        let stroad = &*Box::leak(Stroad::<StroadTestingPayload>::new());
        let _ = stroad.unordered_park_conditionally(list_ent_0, || true);

        let t1 = loom::thread::spawn(move || {
            let _ = stroad.unordered_park_conditionally(list_ent_1, || true);
        });
        let t2 = loom::thread::spawn(move || {
            stroad.unordered_unpark_all(loom_dummy_obj_ref, &mut DebugDummyQueue {});
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
                // unpark happened (uselessly), then park happened

                let hash = hash(loom_dummy_obj_ref);
                let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
                let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 1;

                unsafe {
                    let shard_data = &*stroad.shards[shard as usize].get();
                    assert_eq!(shard_data.capacity_shift, 1);
                    assert_eq!(shard_data.nents, 1);
                    let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
                    assert_ne!(ptr, 0);
                    let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
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
                // both parks happened, then unpark happened

                let hash = hash(loom_dummy_obj_ref);
                let shard = hash & (HASH_NUM_SHARDS as u64 - 1);
                let bucket = (hash >> HASH_NUM_SHARDS_SHIFT) & 0b11;

                unsafe {
                    let shard_data = &*stroad.shards[shard as usize].get();
                    assert_eq!(shard_data.capacity_shift, 2);
                    assert_eq!(shard_data.nents, 0);
                    let ptr = shard_data.buckets_and_lock.load(Ordering::Relaxed) & !1;
                    assert_ne!(ptr, 0);
                    let ptr = ptr as *const StroadBucket<StroadTestingPayload>;
                    let ptr_i = &*(ptr.add(bucket as usize));

                    assert!(ptr_i.wants_lock.next.is_none());
                    assert!(ptr_i.wants_lock.prev.is_none());
                }
            }
        }
    })
}
