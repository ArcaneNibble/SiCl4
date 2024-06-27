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
