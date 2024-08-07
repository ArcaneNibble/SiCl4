use super::*;

fn assert_send<T: Send>() {}
fn assert_sync<T: Sync>() {}

#[test]
fn commit_queue_item_ordering() {
    assert_eq!(
        ItemWithPriority { item: 123, prio: 1 },
        ItemWithPriority { item: 456, prio: 1 }
    );
    assert_ne!(
        ItemWithPriority { item: 123, prio: 1 },
        ItemWithPriority { item: 123, prio: 2 }
    );
    assert!(ItemWithPriority { item: 123, prio: 1 } > ItemWithPriority { item: 123, prio: 2 });
}

#[test]
fn ensure_commit_queue_send_sync() {
    assert_send::<OrderedCommitQueue<&()>>();
    assert_sync::<OrderedCommitQueue<&()>>();
}

#[cfg(loom)]
#[test]
fn commit_queue_loom_smoke_test() {
    use std::mem::MaybeUninit;

    const INITIAL_PRIORITIES: usize = 2;
    const ITEMS_AT_PRIORITY: usize = 2;
    const NEW_ITERS: usize = 1;

    #[derive(Debug)]
    struct TestWork {
        _state: TestWorkState,
        idx: usize,
    }

    #[derive(Debug)]
    enum TestWorkState {
        New,
        LocksGrabbed,
    }

    fn thread_func(tid: usize, done: &[AtomicBool], q: &OrderedCommitQueue<TestWork>) {
        while let Some(item) = q.get_some_work(tid) {
            // dbg!(&item);
            if item.prio <= q.commit_priority() {
                if item.prio < (INITIAL_PRIORITIES * NEW_ITERS) as i64 {
                    q.create_new_work(
                        (
                            TestWork {
                                _state: TestWorkState::New,
                                idx: item.item.idx,
                            },
                            item.prio + INITIAL_PRIORITIES as i64,
                        )
                            .into(),
                    );
                }

                let old_done = done[item.prio as usize * ITEMS_AT_PRIORITY + item.item.idx]
                    .swap(true, Ordering::Relaxed);
                assert!(!old_done);

                q.finish_work(tid, item);
            } else {
                q.put_back_waiting_item(
                    tid,
                    (
                        TestWork {
                            _state: TestWorkState::LocksGrabbed,
                            idx: item.item.idx,
                        },
                        item.prio,
                    )
                        .into(),
                );
            }
        }
    }

    loom::model(|| {
        println!("~~~~~~~~~~ ITER ~~~~~~~~~~");

        let mut done: [MaybeUninit<AtomicBool>;
            INITIAL_PRIORITIES * ITEMS_AT_PRIORITY * (1 + NEW_ITERS)] =
            unsafe { MaybeUninit::uninit().assume_init() };
        for x in &mut done[..] {
            x.write(AtomicBool::new(false));
        }
        let done = unsafe {
            std::mem::transmute::<
                _,
                [AtomicBool; INITIAL_PRIORITIES * ITEMS_AT_PRIORITY * (1 + NEW_ITERS)],
            >(done)
        };
        let done = &*Box::leak(Box::new(done));
        let q = &*Box::leak(Box::new(OrderedCommitQueue::<TestWork>::new()));

        for prio in 0..INITIAL_PRIORITIES {
            for idx in 0..ITEMS_AT_PRIORITY {
                q.create_new_work(
                    (
                        TestWork {
                            _state: TestWorkState::New,
                            idx,
                        },
                        prio as i64,
                    )
                        .into(),
                );
            }
        }

        let t1 = loom::thread::spawn(move || thread_func(0, done, &q));
        let t2 = loom::thread::spawn(move || thread_func(1, done, &q));

        t1.join().unwrap();
        t2.join().unwrap();

        for (i, x) in done.iter().enumerate() {
            let xb = x.load(Ordering::Relaxed);
            if !xb {
                println!("item {i} not done!");
            }
            assert!(xb);
        }
    });
}
