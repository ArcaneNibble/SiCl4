//! Manage work items for ordered algorithms

use std::collections::BinaryHeap;
use std::fmt::Debug;
use std::sync::atomic::Ordering;

use tracing::Level;

use crate::loom_testing::*;

pub const MAX_THREADS: usize = 64;

/// Struct holding payload and a priority, where traits are implemented
/// s.t. equality and ordering *only* look at the priority, and
/// s.t. ordering is inverted for turning a max-heap into a min-heap
///
/// (This implies that two items with the same priority but different payloads
/// *will* compare equal with `==` even if the payloads are different).
#[derive(Clone, Copy, Debug, Hash, Default)]
pub struct ItemWithPriority<T> {
    pub item: T,
    pub prio: i64,
}
impl<T> ItemWithPriority<T> {
    pub fn new(item: T, prio: i64) -> Self {
        Self { item, prio }
    }
}
impl<T> From<(T, i64)> for ItemWithPriority<T> {
    fn from(value: (T, i64)) -> Self {
        Self {
            item: value.0,
            prio: value.1,
        }
    }
}
impl<T> PartialEq for ItemWithPriority<T> {
    fn eq(&self, other: &Self) -> bool {
        self.prio == other.prio
    }
}
impl<T> Eq for ItemWithPriority<T> {}
impl<T> Ord for ItemWithPriority<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.prio.cmp(&self.prio)
    }
}
impl<T> PartialOrd for ItemWithPriority<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug)]
struct QueueInnards<T> {
    /// priority of whatever's been handed out to each thread
    wip_priority: [i64; MAX_THREADS],
    /// work that is not started i.e. no locks grabbed
    items_not_started: BinaryHeap<ItemWithPriority<T>>,
    /// work that has locks grabbed but isn't allowed to commit yet
    /// (because its priority hasn't been reached)
    items_waiting: BinaryHeap<ItemWithPriority<T>>,
}
impl<T> QueueInnards<T> {
    pub fn new() -> Self {
        Self {
            wip_priority: [i64::MAX; MAX_THREADS],
            items_not_started: BinaryHeap::new(),
            items_waiting: BinaryHeap::new(),
        }
    }
}

#[derive(Debug)]
pub struct OrderedCommitQueue<T> {
    inside: Mutex<QueueInnards<T>>,
    wait_not_empty: Condvar,
    commit_priority: AtomicUsize,
}
impl<T: Debug> OrderedCommitQueue<T> {
    pub fn new() -> Self {
        Self {
            inside: Mutex::new(QueueInnards::new()),
            wait_not_empty: Condvar::new(),
            commit_priority: AtomicUsize::new(0),
        }
    }

    #[inline]
    pub fn commit_priority(&self) -> i64 {
        self.commit_priority.load(Ordering::Relaxed) as i64
    }

    pub fn create_new_work(&self, item: ItemWithPriority<T>) {
        debug_assert!(item.prio >= 0 && item.prio < i64::MAX);
        let mut inside = self.inside.lock().unwrap();
        tracing::event!(
            name: "ordered_commit_queue::create_new_work",
            Level::TRACE,
            item = ?item,
        );
        inside.items_not_started.push(item);
        self.wait_not_empty.notify_one();
    }

    pub fn put_back_waiting_item(&self, tid: usize, item: ItemWithPriority<T>) {
        let mut inside = self.inside.lock().unwrap();
        tracing::event!(
            name: "ordered_commit_queue::put_back_waiting_item",
            Level::TRACE,
            tid,
            item = ?item,
        );
        debug_assert_eq!(inside.wip_priority[tid], item.prio);
        inside.wip_priority[tid] = i64::MAX;
        inside.items_waiting.push(item);
    }

    pub fn finish_work(&self, tid: usize, item: ItemWithPriority<T>) {
        let mut inside = self.inside.lock().unwrap();
        tracing::event!(
            name: "ordered_commit_queue::finish_work",
            Level::TRACE,
            tid,
            item = ?item,
        );

        debug_assert_eq!(inside.wip_priority[tid], item.prio);
        inside.wip_priority[tid] = i64::MAX;

        let prev_commit_priority = self.commit_priority();
        debug_assert!(item.prio <= prev_commit_priority); // cannot be committing a higher-priority item, wtf?

        // the next priority has to be somewhere amongst these queues
        let waiting_highest_prio = inside
            .items_waiting
            .peek()
            .map_or_else(|| i64::MAX, |e| e.prio);
        let wip_highest_prio = *inside.wip_priority.iter().min().unwrap();
        let not_started_highest_prio = inside
            .items_not_started
            .peek()
            .map_or_else(|| i64::MAX, |e| e.prio);
        let next_highest_prio = i64::min(
            waiting_highest_prio,
            i64::min(wip_highest_prio, not_started_highest_prio),
        );
        debug_assert!(next_highest_prio >= item.prio);

        self.commit_priority
            .store(next_highest_prio as usize, Ordering::Relaxed);

        tracing::event!(
            name: "ordered_commit_queue::advance_priority",
            Level::TRACE,
            item_priority = item.prio,
            finished_priority = prev_commit_priority,
            new_priority = next_highest_prio,
        );

        if inside.items_not_started.len() == 0
            && inside.items_waiting.len() == 0
            && wip_highest_prio == i64::MAX
        {
            // we just handed in the *last ever* work item
            // tell everybody to go home
            self.wait_not_empty.notify_all();
        }
    }

    pub fn get_some_work(&self, tid: usize) -> Option<ItemWithPriority<T>> {
        let mut inside = self.inside.lock().unwrap();

        loop {
            // iff there's *no* items, there *cannot* be any work left
            // (thread termination condition)
            if inside.items_not_started.len() == 0
                && inside.items_waiting.len() == 0
                && *inside.wip_priority.iter().min().unwrap() == i64::MAX
            {
                return None;
            }

            // first have to check if anything in the "not allowed to commit yet" queue is now allowed
            // (it can become allowed because some work has been handed in)
            if let Some(item) = inside.items_waiting.peek() {
                if item.prio <= self.commit_priority() {
                    let item = inside.items_waiting.pop().unwrap();
                    tracing::event!(
                        name: "ordered_commit_queue::get_some_work",
                        Level::TRACE,
                        work_type = "waiting to commit",
                        item = ?item,
                    );
                    inside.wip_priority[tid] = item.prio;
                    return Some(item);
                }
            }

            // if we got here, either items_waiting is empty or the highest-priority item
            // isn't allowed to commit yet (which means nothing else in there is either)
            // so we try to speculate something
            if let Some(item) = inside.items_not_started.pop() {
                tracing::event!(
                    name: "ordered_commit_queue::get_some_work",
                    Level::TRACE,
                    work_type = "lock grabbing",
                    item = ?item,
                );
                inside.wip_priority[tid] = item.prio;
                return Some(item);
            } else {
                // there's no work to do right now
                tracing::event!(
                    name: "ordered_commit_queue::get_some_work",
                    Level::TRACE,
                    "no work to do! blocking!"
                );
                inside = self.wait_not_empty.wait(inside).unwrap();
            }
        }
    }
}

#[cfg(test)]
mod tests;
