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
    const INITIAL_PRIORITIES: usize = 2;
    const ITEMS_AT_PRIORITY: usize = 1;
    const NEW_ITERS: usize = 1;

    #[derive(Debug)]
    enum TestWorkState {
        New,
        LocksGrabbed,
    }

    fn thread_func(q: &OrderedCommitQueue<TestWorkState>) {
        while let Some(item) = q.get_some_work() {
            // dbg!(&item);
            if item.prio <= q.commit_priority() {
                if item.prio < (INITIAL_PRIORITIES * NEW_ITERS) as i64 {
                    q.create_new_work(
                        (TestWorkState::New, item.prio + INITIAL_PRIORITIES as i64).into(),
                    );
                }

                q.finish_work(item);
            } else {
                q.put_back_waiting_item((TestWorkState::LocksGrabbed, item.prio).into());
            }
        }
    }

    loom::model(|| {
        println!("~~~~~~~~~~ ITER ~~~~~~~~~~");

        let q = &*Box::leak(Box::new(OrderedCommitQueue::<TestWorkState>::new()));

        for prio in 0..INITIAL_PRIORITIES {
            for _i in 0..ITEMS_AT_PRIORITY {
                q.create_new_work((TestWorkState::New, prio as i64).into());
            }
        }

        let t1 = loom::thread::spawn(move || thread_func(&q));
        let t2 = loom::thread::spawn(move || thread_func(&q));

        t1.join().unwrap();
        t2.join().unwrap();
    });
}
