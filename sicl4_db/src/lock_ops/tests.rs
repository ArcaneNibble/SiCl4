use std::alloc::Layout;

use mem::MaybeUninit;

use super::*;

#[derive(Default, Debug)]
struct LockingTestingPayload {
    unparked: AtomicBool,
    cancelled: AtomicBool,
}
impl StroadToWorkItemLink for LockingTestingPayload {
    fn unpark(&self, _: &mut ()) {
        self.unparked.store(true, Ordering::Relaxed);
    }

    fn cancel(&self) {
        self.cancelled.store(true, Ordering::Relaxed);
    }

    type UnparkXtraTy = ();
}

struct JustU32Mapper {}
impl TypeMapper for JustU32Mapper {
    type BinsArrayTy<T> = [T; 1];
    const LAYOUTS: &'static [&'static [Layout]] = &[&[Layout::new::<LockedObj<u32>>()]];
}
impl TypeMappable<JustU32Mapper> for LockedObj<u32> {
    const I: usize = 0;
}
type ObjRefLockedU32<'arena> = ObjRef<'arena, u32>;

#[test]
#[ignore = "not automated, human eye verified"]
fn locking_manual_tests() {
    let alloc = SlabRoot::<JustU32Mapper>::new();
    let thread_shard = alloc.new_thread();
    let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
    let obj = unsafe {
        let obj_p = obj.as_mut_ptr();
        (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
        (*obj_p).num_rw = UnsafeCell::new(0);
        (*obj_p).payload = UnsafeCell::new(12345);
        obj.assume_init_ref()
    };
    dbg!(&obj);
    let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
    dbg!(&obj_ref);

    let stroad = Stroad::<LockingTestingPayload>::new();

    let mut lock = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    #[allow(unused_mut)]
    let mut lock = unsafe {
        LockAndStroadData::init(lock.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock.assume_init()
    };

    dbg!(&lock);
    let ret = lock.unordered_try_write(&stroad);
    dbg!(&ret);
    let _ = ret.is_ok();
    dbg!(&lock);

    unsafe {
        lock.unlock(&stroad, &mut ());
    }
    dbg!(&lock);

    // can't work
    // let mut _lock2 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    // let mut _lock2 = unsafe {
    //     LockAndStroadData::init(_lock2.as_mut_ptr(), obj_ref.type_erase());
    //     (*(*_lock2.as_mut_ptr()).stroad_state.get()).work_item_link =
    //         LockingTestingPayload::default();
    //     _lock2.assume_init()
    // };
    // std::mem::swap(&mut lock, &mut _lock2);
}

#[cfg(loom)]
#[test]
fn locking_loom_unordered_ww_nounlock() {
    loom::model(|| {
        let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustU32Mapper>::new()));
        let thread_shard = alloc.new_thread();
        let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
        let obj = unsafe {
            let obj_p = obj.as_mut_ptr();
            (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
            (*obj_p).num_rw = UnsafeCell::new(0);
            (*obj_p).payload = UnsafeCell::new(12345);
            obj.assume_init_ref()
        };
        let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
        drop(thread_shard);
        let stroad = &*Box::leak(Stroad::<LockingTestingPayload>::new());

        let lock_0 = Box::leak(Box::new(MaybeUninit::<
            LockAndStroadData<'_, '_, LockingTestingPayload>,
        >::uninit()));
        let lock_0 = unsafe {
            LockAndStroadData::init(lock_0.as_mut_ptr(), obj_ref.type_erase());
            (*(*lock_0.as_mut_ptr()).stroad_state.get()).work_item_link =
                LockingTestingPayload::default();
            lock_0.assume_init_mut()
        };
        let lock_1 = Box::leak(Box::new(MaybeUninit::<
            LockAndStroadData<'_, '_, LockingTestingPayload>,
        >::uninit()));
        let lock_1 = unsafe {
            LockAndStroadData::init(lock_1.as_mut_ptr(), obj_ref.type_erase());
            (*(*lock_1.as_mut_ptr()).stroad_state.get()).work_item_link =
                LockingTestingPayload::default();
            lock_1.assume_init_mut()
        };

        let t1_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));
        let t2_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));

        let t1 = loom::thread::spawn(move || {
            let ret = lock_0.unordered_try_write(stroad);

            assert!(ret.is_ok());
            t1_got_lock.store(ret.unwrap(), Ordering::Relaxed);
        });
        let t2 = loom::thread::spawn(move || {
            let ret = lock_1.unordered_try_write(stroad);

            assert!(ret.is_ok());
            t2_got_lock.store(ret.unwrap(), Ordering::Relaxed);
        });

        t1.join().unwrap();
        t2.join().unwrap();

        let t1_got_lock = t1_got_lock.load(Ordering::Relaxed);
        let t2_got_lock = t2_got_lock.load(Ordering::Relaxed);

        // one of the two *must* succeed
        assert!(t1_got_lock != t2_got_lock);
    });
}

#[cfg(loom)]
#[test]
fn locking_loom_unordered_rw_nounlock() {
    loom::model(|| {
        let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustU32Mapper>::new()));
        let thread_shard = alloc.new_thread();
        let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
        let obj = unsafe {
            let obj_p = obj.as_mut_ptr();
            (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
            (*obj_p).num_rw = UnsafeCell::new(0);
            (*obj_p).payload = UnsafeCell::new(12345);
            obj.assume_init_ref()
        };
        let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
        drop(thread_shard);
        let stroad = &*Box::leak(Stroad::<LockingTestingPayload>::new());

        let lock_0 = Box::leak(Box::new(MaybeUninit::<
            LockAndStroadData<'_, '_, LockingTestingPayload>,
        >::uninit()));
        let lock_0 = unsafe {
            LockAndStroadData::init(lock_0.as_mut_ptr(), obj_ref.type_erase());
            (*(*lock_0.as_mut_ptr()).stroad_state.get()).work_item_link =
                LockingTestingPayload::default();
            lock_0.assume_init_mut()
        };
        let lock_1 = Box::leak(Box::new(MaybeUninit::<
            LockAndStroadData<'_, '_, LockingTestingPayload>,
        >::uninit()));
        let lock_1 = unsafe {
            LockAndStroadData::init(lock_1.as_mut_ptr(), obj_ref.type_erase());
            (*(*lock_1.as_mut_ptr()).stroad_state.get()).work_item_link =
                LockingTestingPayload::default();
            lock_1.assume_init_mut()
        };

        let t1_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));
        let t2_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));

        let t1 = loom::thread::spawn(move || {
            let ret = lock_0.unordered_try_read(stroad);

            assert!(ret.is_ok());
            t1_got_lock.store(ret.unwrap(), Ordering::Relaxed);
        });
        let t2 = loom::thread::spawn(move || {
            let ret = lock_1.unordered_try_write(stroad);

            assert!(ret.is_ok());
            t2_got_lock.store(ret.unwrap(), Ordering::Relaxed);
        });

        t1.join().unwrap();
        t2.join().unwrap();

        let t1_got_lock = t1_got_lock.load(Ordering::Relaxed);
        let t2_got_lock = t2_got_lock.load(Ordering::Relaxed);

        // one of the two *must* succeed
        assert!(t1_got_lock != t2_got_lock);
    });
}

#[cfg(loom)]
#[test]
fn locking_loom_unordered_rr_nounlock() {
    loom::model(|| {
        let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustU32Mapper>::new()));
        let thread_shard = alloc.new_thread();
        let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
        let obj = unsafe {
            let obj_p = obj.as_mut_ptr();
            (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
            (*obj_p).num_rw = UnsafeCell::new(0);
            (*obj_p).payload = UnsafeCell::new(12345);
            obj.assume_init_ref()
        };
        let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
        drop(thread_shard);
        let stroad = &*Box::leak(Stroad::<LockingTestingPayload>::new());

        let lock_0 = Box::leak(Box::new(MaybeUninit::<
            LockAndStroadData<'_, '_, LockingTestingPayload>,
        >::uninit()));
        let lock_0 = unsafe {
            LockAndStroadData::init(lock_0.as_mut_ptr(), obj_ref.type_erase());
            (*(*lock_0.as_mut_ptr()).stroad_state.get()).work_item_link =
                LockingTestingPayload::default();
            lock_0.assume_init_mut()
        };
        let lock_1 = Box::leak(Box::new(MaybeUninit::<
            LockAndStroadData<'_, '_, LockingTestingPayload>,
        >::uninit()));
        let lock_1 = unsafe {
            LockAndStroadData::init(lock_1.as_mut_ptr(), obj_ref.type_erase());
            (*(*lock_1.as_mut_ptr()).stroad_state.get()).work_item_link =
                LockingTestingPayload::default();
            lock_1.assume_init_mut()
        };

        let t1_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));
        let t2_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));

        let t1 = loom::thread::spawn(move || {
            let ret = lock_0.unordered_try_read(stroad);

            assert!(ret.is_ok());
            t1_got_lock.store(ret.unwrap(), Ordering::Relaxed);
        });
        let t2 = loom::thread::spawn(move || {
            let ret = lock_1.unordered_try_read(stroad);

            assert!(ret.is_ok());
            t2_got_lock.store(ret.unwrap(), Ordering::Relaxed);
        });

        t1.join().unwrap();
        t2.join().unwrap();

        let t1_got_lock = t1_got_lock.load(Ordering::Relaxed);
        let t2_got_lock = t2_got_lock.load(Ordering::Relaxed);

        // *both* must succeed
        assert!(t1_got_lock && t2_got_lock);
    });
}

#[cfg(loom)]
#[test]
fn locking_loom_unordered_ww_unlock() {
    loom::model(|| {
        let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustU32Mapper>::new()));
        let thread_shard = alloc.new_thread();
        let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
        let obj = unsafe {
            let obj_p = obj.as_mut_ptr();
            (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
            (*obj_p).num_rw = UnsafeCell::new(0);
            (*obj_p).payload = UnsafeCell::new(12345);
            obj.assume_init_ref()
        };
        let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
        drop(thread_shard);
        let stroad = &*Box::leak(Stroad::<LockingTestingPayload>::new());

        let lock_0 = Box::leak(Box::new(MaybeUninit::<
            LockAndStroadData<'_, '_, LockingTestingPayload>,
        >::uninit()));
        let lock_0 = unsafe {
            LockAndStroadData::init(lock_0.as_mut_ptr(), obj_ref.type_erase());
            (*(*lock_0.as_mut_ptr()).stroad_state.get()).work_item_link =
                LockingTestingPayload::default();
            lock_0.assume_init_mut()
        };
        let lock_1 = Box::leak(Box::new(MaybeUninit::<
            LockAndStroadData<'_, '_, LockingTestingPayload>,
        >::uninit()));
        let lock_1 = unsafe {
            LockAndStroadData::init(lock_1.as_mut_ptr(), obj_ref.type_erase());
            (*(*lock_1.as_mut_ptr()).stroad_state.get()).work_item_link =
                LockingTestingPayload::default();
            lock_1.assume_init_mut()
        };

        let t1_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));
        let t2_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));

        let t1_lock = &*lock_0;
        let t2_lock = &*lock_1;

        // println!("~~~~~ MODEL ITER ~~~~~");

        let t1 = loom::thread::spawn(move || {
            let ret = t1_lock.unordered_try_write(stroad);

            assert!(ret.is_ok());
            if ret.unwrap() {
                t1_got_lock.store(true, Ordering::Relaxed);
                // needed in order to simulate processing taking some time
                loom::thread::yield_now();
                unsafe {
                    t1_lock.unlock(stroad, &mut ());
                }
            }
        });
        let t2 = loom::thread::spawn(move || {
            let ret = t2_lock.unordered_try_write(stroad);

            assert!(ret.is_ok());
            if ret.unwrap() {
                t2_got_lock.store(true, Ordering::Relaxed);
                // needed in order to simulate processing taking some time
                loom::thread::yield_now();
                // drop guard
                unsafe {
                    t2_lock.unlock(stroad, &mut ());
                }
            }
        });

        t1.join().unwrap();
        t2.join().unwrap();

        let t1_got_lock = t1_got_lock.load(Ordering::Relaxed);
        let t2_got_lock = t2_got_lock.load(Ordering::Relaxed);
        // xxx
        unsafe {
            match (t1_got_lock, t2_got_lock) {
                (true, true) => {
                    assert!(!(*t1_lock.stroad_state.get())
                        .work_item_link
                        .unparked
                        .load(Ordering::Relaxed));
                    assert!(!(*t1_lock.stroad_state.get())
                        .work_item_link
                        .cancelled
                        .load(Ordering::Relaxed));
                    assert!(!(*t2_lock.stroad_state.get())
                        .work_item_link
                        .unparked
                        .load(Ordering::Relaxed));
                    assert!(!(*t2_lock.stroad_state.get())
                        .work_item_link
                        .cancelled
                        .load(Ordering::Relaxed));
                }
                (true, false) => {
                    assert!(!(*t1_lock.stroad_state.get())
                        .work_item_link
                        .unparked
                        .load(Ordering::Relaxed));
                    assert!(!(*t1_lock.stroad_state.get())
                        .work_item_link
                        .cancelled
                        .load(Ordering::Relaxed));
                    assert!((*t2_lock.stroad_state.get())
                        .work_item_link
                        .unparked
                        .load(Ordering::Relaxed));
                    assert!(!(*t2_lock.stroad_state.get())
                        .work_item_link
                        .cancelled
                        .load(Ordering::Relaxed));
                }
                (false, true) => {
                    assert!((*t1_lock.stroad_state.get())
                        .work_item_link
                        .unparked
                        .load(Ordering::Relaxed));
                    assert!(!(*t1_lock.stroad_state.get())
                        .work_item_link
                        .cancelled
                        .load(Ordering::Relaxed));
                    assert!(!(*t2_lock.stroad_state.get())
                        .work_item_link
                        .unparked
                        .load(Ordering::Relaxed));
                    assert!(!(*t2_lock.stroad_state.get())
                        .work_item_link
                        .cancelled
                        .load(Ordering::Relaxed));
                }
                (false, false) => {
                    panic!("both locks failed to grab")
                }
            }
        }
    });
}
// fixme: the cas loop makes thw _rw_unlock and _rr_unlock tests too slow

#[cfg(not(loom))]
#[test]
fn locking_single_threaded_write_unpark_sim() {
    let alloc = SlabRoot::<JustU32Mapper>::new();
    let thread_shard = alloc.new_thread();
    let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
    let obj = unsafe {
        let obj_p = obj.as_mut_ptr();
        (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
        (*obj_p).num_rw = UnsafeCell::new(0);
        (*obj_p).payload = UnsafeCell::new(12345);
        obj.assume_init_ref()
    };
    let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
    drop(thread_shard);

    let stroad = Stroad::<LockingTestingPayload>::new();

    let mut lock_0 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_0 = unsafe {
        LockAndStroadData::init(lock_0.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_0.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_0.assume_init()
    };
    let ret = lock_0.unordered_try_write(&stroad);
    assert_eq!(ret, Ok(true));
    assert_eq!(
        obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
        0x800000000000007f | (gen << 8)
    );

    let mut lock_1 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_1 = unsafe {
        LockAndStroadData::init(lock_1.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_1.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_1.assume_init()
    };
    let ret = lock_1.unordered_try_write(&stroad);
    assert_eq!(ret, Ok(false));
    assert_eq!(
        obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
        0x80000000000000ff | (gen << 8)
    );

    unsafe {
        lock_0.unlock(&stroad, &mut ());
        assert_eq!(
            obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
            0x8000000000000000 | (gen << 8)
        );
        assert!((*lock_1.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
    }
}

#[cfg(not(loom))]
#[test]
fn locking_single_threaded_read_unpark_sim() {
    let alloc = SlabRoot::<JustU32Mapper>::new();
    let thread_shard = alloc.new_thread();
    let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
    let obj = unsafe {
        let obj_p = obj.as_mut_ptr();
        (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
        (*obj_p).num_rw = UnsafeCell::new(0);
        (*obj_p).payload = UnsafeCell::new(12345);
        obj.assume_init_ref()
    };
    let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
    drop(thread_shard);

    let stroad = Stroad::<LockingTestingPayload>::new();

    let mut lock_0 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_0 = unsafe {
        LockAndStroadData::init(lock_0.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_0.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_0.assume_init()
    };
    let ret = lock_0.unordered_try_read(&stroad);
    assert_eq!(ret, Ok(true));
    assert_eq!(
        obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
        0x8000000000000001 | (gen << 8)
    );

    let mut lock_1 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_1 = unsafe {
        LockAndStroadData::init(lock_1.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_1.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_1.assume_init()
    };
    let ret = lock_1.unordered_try_read(&stroad);
    assert_eq!(ret, Ok(true));
    assert_eq!(
        obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
        0x8000000000000002 | (gen << 8)
    );

    let mut lock_2 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_2 = unsafe {
        LockAndStroadData::init(lock_2.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_2.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_2.assume_init()
    };
    let ret = lock_2.unordered_try_write(&stroad);
    assert_eq!(ret, Ok(false));
    assert_eq!(
        obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
        0x8000000000000082 | (gen << 8)
    );

    unsafe {
        lock_0.unlock(&stroad, &mut ());
        assert!(!(*lock_2.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
        assert_eq!(
            obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
            0x8000000000000081 | (gen << 8)
        );
        lock_1.unlock(&stroad, &mut ());
        assert!((*lock_2.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
        assert_eq!(
            obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
            0x8000000000000000 | (gen << 8)
        );
    }
}

#[cfg(not(loom))]
#[test]
fn locking_single_threaded_ordered_write_causes_unpark_sim() {
    let alloc = SlabRoot::<JustU32Mapper>::new();
    let thread_shard = alloc.new_thread();
    let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
    let obj = unsafe {
        let obj_p = obj.as_mut_ptr();
        (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
        (*obj_p).num_rw = UnsafeCell::new(0);
        (*obj_p).payload = UnsafeCell::new(12345);
        obj.assume_init_ref()
    };
    let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
    drop(thread_shard);

    let stroad = Stroad::<LockingTestingPayload>::new();

    let mut lock_0 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_0 = unsafe {
        LockAndStroadData::init(lock_0.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_0.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_0.assume_init()
    };
    let ret = lock_0.ordered_try_read(&stroad, 0);
    assert_eq!(ret, Ok(true));
    assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 1);

    let mut lock_1 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_1 = unsafe {
        LockAndStroadData::init(lock_1.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_1.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_1.assume_init()
    };
    let ret = lock_1.ordered_try_write(&stroad, 1);
    assert_eq!(ret, Ok(true));
    assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

    let mut lock_2 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_2 = unsafe {
        LockAndStroadData::init(lock_2.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_2.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_2.assume_init()
    };
    let ret = lock_2.ordered_try_read(&stroad, 2);
    assert_eq!(ret, Ok(false));
    assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

    unsafe {
        // the read shouldn't trigger an unpark
        lock_0.unlock(&stroad, &mut ());
        assert!(!(*lock_2.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
        assert_eq!(*obj_ref.ptr.num_rw.get(), 0x8000000000000000);
        // but the write should
        lock_1.unlock(&stroad, &mut ());
        assert!((*lock_2.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
        assert_eq!(*obj_ref.ptr.num_rw.get(), 0);
    }
}

#[cfg(not(loom))]
#[test]
fn locking_single_threaded_ordered_read_causes_unpark_sim() {
    let alloc = SlabRoot::<JustU32Mapper>::new();
    let thread_shard = alloc.new_thread();
    let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
    let obj = unsafe {
        let obj_p = obj.as_mut_ptr();
        (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
        (*obj_p).num_rw = UnsafeCell::new(0);
        (*obj_p).payload = UnsafeCell::new(12345);
        obj.assume_init_ref()
    };
    let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
    drop(thread_shard);

    let stroad = Stroad::<LockingTestingPayload>::new();

    let mut lock_0 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_0 = unsafe {
        LockAndStroadData::init(lock_0.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_0.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_0.assume_init()
    };
    let ret = lock_0.ordered_try_read(&stroad, 0);
    assert_eq!(ret, Ok(true));
    assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 1);

    let mut lock_1 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_1 = unsafe {
        LockAndStroadData::init(lock_1.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_1.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_1.assume_init()
    };
    let ret = lock_1.ordered_try_write(&stroad, 1);
    assert_eq!(ret, Ok(true));
    assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

    let mut lock_2 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_2 = unsafe {
        LockAndStroadData::init(lock_2.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_2.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_2.assume_init()
    };
    let ret = lock_2.ordered_try_read(&stroad, 2);
    assert_eq!(ret, Ok(false));
    assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

    let mut lock_3 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_3 = unsafe {
        LockAndStroadData::init(lock_3.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_3.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_3.assume_init()
    };
    let ret = lock_3.ordered_try_read(&stroad, 3);
    assert_eq!(ret, Ok(false));
    assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

    let mut lock_4 = MaybeUninit::<LockAndStroadData<'_, '_, LockingTestingPayload>>::uninit();
    let lock_4 = unsafe {
        LockAndStroadData::init(lock_4.as_mut_ptr(), obj_ref.type_erase());
        (*(*lock_4.as_mut_ptr()).stroad_state.get()).work_item_link =
            LockingTestingPayload::default();
        lock_4.assume_init()
    };
    let ret = lock_4.ordered_try_write(&stroad, 3);
    assert_eq!(ret, Ok(false));
    assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

    unsafe {
        lock_0.unlock(&stroad, &mut ());
        // shouldn't unpark anything yet
        assert_eq!(*obj_ref.ptr.num_rw.get(), 0x8000000000000000);
        assert!(!(*lock_2.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
        assert!(!(*lock_3.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
        assert!(!(*lock_4.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));

        lock_1.unlock(&stroad, &mut ());
        assert_eq!(*obj_ref.ptr.num_rw.get(), 0);
        // both of these should now be unparked
        assert!((*lock_2.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
        assert!((*lock_3.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
        // but not this
        assert!(!(*lock_4.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));

        // xxx simulate 2 and 3 getting re-acquired
        lock_2.state.set(LockState::Unlocked);
        lock_3.state.set(LockState::Unlocked);
        let ret = lock_2.ordered_try_read(&stroad, 2);
        assert_eq!(ret, Ok(true));
        assert_eq!(*obj_ref.ptr.num_rw.get(), 1);
        let ret = lock_3.ordered_try_read(&stroad, 2);
        assert_eq!(ret, Ok(true));
        assert_eq!(*obj_ref.ptr.num_rw.get(), 2);

        lock_2.unlock(&stroad, &mut ());
        // shouldn't unpark yet
        assert_eq!(*obj_ref.ptr.num_rw.get(), 1);
        assert!(!(*lock_4.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));

        lock_3.unlock(&stroad, &mut ());
        // now it should
        assert_eq!(*obj_ref.ptr.num_rw.get(), 0);
        assert!((*lock_4.stroad_state.get())
            .work_item_link
            .unparked
            .load(Ordering::Relaxed));
    }
}
