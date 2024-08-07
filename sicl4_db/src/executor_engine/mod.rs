//! Code for controlling the running of algorithms against netlists

use std::cell::{RefCell, UnsafeCell};
use std::mem::MaybeUninit;
use std::rc::Rc;
use std::sync::atomic::Ordering;
use std::thread;
use std::{cell::Cell, fmt::Debug};

use netlist::*;
use ordered::{OrderedAlgorithm, OrderedAlgorithmROView, OrderedAlgorithmRWView};
use ordered_commit_queue::ItemWithPriority;
use single_threaded::SingleThreadedView;
use tracing::Level;
use unordered::{UnorderedAlgorithm, UnorderedAlgorithmROView, UnorderedAlgorithmRWView};

use crate::allocator::SlabRoot;
use crate::lock_ops::stroad::{Stroad, WorkItemInterface};
use crate::lock_ops::{LockAndStroadData, LockState, TypeErasedObjRef};
use crate::loom_testing::*;
use crate::netlist::*;
use crate::util::UsizePtr;

pub mod netlist;
pub mod ordered;
pub mod ordered_commit_queue;
pub mod single_threaded;
pub mod unordered;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum SpeculativeLockGrabResult {
    /// This work item should block, as it tried to grab an item that is currently in use.
    /// The other thing will tell us when it's done, and there's no point in retrying before then.
    Block,
    /// Whilst trying to get a lock, somebody else came in and told us to cancel.
    /// We have no idea when we can retry. The thing causing the cancellation wants to write to
    /// data that we might've read, so we have to start over.
    Cancel,
}

/// Common API for speculatively grabbing locks on a netlist
pub trait NetlistROView<'arena> {
    /// Try to get a lock on a cell
    ///
    /// Returns:
    /// * `Err(e)` - lock contention
    /// * `Ok(None)` - object is gone, deleted, don't try again
    /// * `Ok(Some(x))` - locked the thing
    fn try_lock_cell<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
        want_write: bool,
    ) -> Result<Option<ROGuard<'arena, NetlistCell<'arena>>>, SpeculativeLockGrabResult>;

    /// Try to get a lock on a wire
    ///
    /// See [Self::try_lock_cell]
    fn try_lock_wire<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistWireRef<'arena>,
        want_write: bool,
    ) -> Result<Option<ROGuard<'arena, NetlistWire<'arena>>>, SpeculativeLockGrabResult>;
}

/// Common API for doing stuff to a netlist
pub trait NetlistRWView<'arena> {
    fn new_cell<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
    ) -> RWGuard<'arena, NetlistCell<'arena>>;
    fn new_wire<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
    ) -> RWGuard<'arena, NetlistWire<'arena>>;
    fn delete_cell<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        guard: RWGuard<'arena, NetlistCell<'arena>>,
    );
    fn delete_wire<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        guard: RWGuard<'arena, NetlistWire<'arena>>,
    );

    fn get_cell_read<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
    ) -> ROGuard<'arena, NetlistCell<'arena>>;
    fn get_cell_write<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
    ) -> RWGuard<'arena, NetlistCell<'arena>>;

    fn get_wire_read<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistWireRef<'arena>,
    ) -> ROGuard<'arena, NetlistWire<'arena>>;
    fn get_wire_write<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistWireRef<'arena>,
    ) -> RWGuard<'arena, NetlistWire<'arena>>;

    fn allocate_new_work<'wrapper>(
        &'wrapper mut self,
        node: NetlistRef<'arena>,
        prio: u64,
    ) -> &'arena mut WorkItem<'arena, 'arena>;
}

/// This many locks are stored in a work item
///
/// TODO: spill extra locks into another heap block?
const MAX_LOCKS_PER_WORK_ITEM: usize = 8;

const WORK_STATUS_DOING_CANCEL: u64 = 1 << 63;
const WORK_STATUS_DOING_ORDERED_COMMIT: u64 = 1 << 62;
const WORK_STATUS_UNPARK_TRIGGERED: u64 = 1 << 61;
const WORK_STATUS_FINISHED_PARKING: u64 = 1 << 60;
const WORK_STATUS_GRABBED_LOCKS: u64 = 1 << 59;
const WORK_STATUS_NUM_LOCKS_MASK: u64 = (1 << 48) - 1;

// TODO
pub struct WorkItem<'arena, 'work_item> {
    seed_node: NetlistRef<'arena>,
    prio: u64,

    /// * `bits[63]`    -- doing a cancel
    ///     - this is used only for ordered algorithms
    ///     - needed so that only *one* concurrent cancel takes effect
    ///     - needed so that, if the work is currently being worked on, next attempts to do anything will fail
    /// * `bits[62]`    -- doing the commit phase of an ordered algorithm
    ///     - needed so that attempts to cancel it at this point become futile (i.e. spin)
    ///     - not used for unordered algorithms because canceling doesn't happen
    /// * `bits[61]`    -- unpark triggered
    ///     - signal an (early) unpark, if thread doing the work hasn't finished abandoning locks yet when unpark is triggered
    /// * `bits[60]`    -- parking finished
    ///     - indicates, along with the above bit, which thread is responsible for handling re-queuing from an unpark
    /// * `bits[59]`    -- ordered algorithm speculative lock grabbing phase complete
    ///     - XXX not sure if this needs to be atomic with everything else, but doing so is easier to reason about
    /// * `bits[47:0]`  -- number of locks
    ///     - needs to be atomic with flags related to cancellation, as cancelling involves concurrent access to the locks
    ///     (i.e. creating new locks from thread A, deleting locks from a cancelling thread B)
    ///
    /// See the <TODO DRAW/UPLOAD THESE> diagrams for details.
    status: AtomicU64,

    locks: [MaybeUninit<
        UnsafeCell<LockAndStroadData<'arena, 'work_item, WorkItemPerLockData<'arena, 'work_item>>>,
    >; MAX_LOCKS_PER_WORK_ITEM],
}
// safety: we carefully make sure unpark/cancel have correct thread-safety
unsafe impl<'arena, 'work_item> Send for WorkItem<'arena, 'work_item> {}
unsafe impl<'arena, 'work_item> Sync for WorkItem<'arena, 'work_item> {}
impl<'arena, 'work_item> Debug for WorkItem<'arena, 'work_item> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WorkItem")
            .field("seed_node", &self.seed_node)
            .field("prio", &self.prio)
            .field("status", &self.status)
            .finish()
    }
}

impl<'arena, 'work_item> WorkItem<'arena, 'work_item> {
    pub unsafe fn init(
        self_: *mut Self,
        node: NetlistRef<'arena>,
        prio: u64,
    ) -> &'work_item mut Self {
        (*self_).seed_node = node;
        (*self_).prio = prio;
        (*self_).status = AtomicU64::new(0);
        &mut *self_
    }

    fn unpark<Q: WorkQueueInterface<WorkItemTy = &'work_item Self>>(&'work_item self, q: &mut Q) {
        // unpark happens *only* on lock release
        // and *only* happens once
        // it happens for both ordered and unordered algorithms
        // it cannot happen multiple times simultaneously from different threads, because
        // a work item can only be blocked on *one* lock at a time (at least in a correct impl).
        // additionally, unparking happens with the stroad bucket lock held -- can only happen from one thread

        let old_status = self
            .status
            .fetch_or(WORK_STATUS_UNPARK_TRIGGERED, Ordering::Relaxed);
        // cannot be parked if we've gotten to these states
        debug_assert!(old_status & WORK_STATUS_DOING_ORDERED_COMMIT == 0);
        debug_assert!(old_status & WORK_STATUS_GRABBED_LOCKS == 0);
        // unpark cannot happen more than once
        debug_assert!(old_status & WORK_STATUS_UNPARK_TRIGGERED == 0);

        if old_status & WORK_STATUS_DOING_CANCEL != 0 {
            tracing::event!(
                name: "work_item::unpark_cancelled",
                Level::TRACE,
                unparked_work = ?UsizePtr::from(self)
            );
            // unpark and cancel are happening *at the same time*
            // this can only happen if:
            //  * this node is holding multiple locks
            //  * this node tried to grab a lock, but failed and decided it's going to wait (parking)
            //  * this node is now trying to unwind the locks it does have
            //  * before this finishes, an unpark is triggered (from another thread)
            //      * if parking were finished, the item isn't holding any locks and cannot be cancelled
            debug_assert!(old_status & WORK_STATUS_FINISHED_PARKING == 0);
            //  * at the same time, a cancel is triggered (from a third thread)

            // in any case, let the responsibility of re-queuing this work fall to the thread doing the cancel
            // (i.e. don't do anything here)
        } else if old_status & WORK_STATUS_FINISHED_PARKING == 0 {
            tracing::event!(
                name: "work_item::unpark_tooearly",
                Level::TRACE,
                unparked_work = ?UsizePtr::from(self)
            );
            // unpark called, but parking isn't actually finished yet
            // let the parking thread be responsible for re-queuing (i.e. don't do anything here)
        } else {
            // println!("unparked");
            tracing::event!(
                name: "work_item::unpark",
                Level::TRACE,
                unparked_work = ?UsizePtr::from(self)
            );
            // we are doing the unpark here
            q.add_work(self);
        }
    }

    fn cancel<Q: WorkQueueInterface<WorkItemTy = &'work_item Self>>(&'work_item self, q: &mut Q) {
        // cancel happens *only* on lock acquisition
        // it happens *only* for ordered algorithms
        // it can happen multiple times in a multithreaded race-prone way, because
        // even though cancelling happens with the stroad bucket lock held,
        // a speculative work item waiting to commit can hold multiple *different* locks.
        // a cancellation can be triggered because of two *different* ones in a racy way

        let mut old_status = self
            .status
            .fetch_or(WORK_STATUS_DOING_CANCEL, Ordering::Relaxed);

        // if this bit gets set, it is too late. we have to wait for this to finish
        if old_status & WORK_STATUS_DOING_ORDERED_COMMIT != 0 {
            tracing::event!(
                name: "work_item::cancel_toolate_spin",
                Level::TRACE,
                work = ?UsizePtr::from(self)
            );

            while old_status & WORK_STATUS_DOING_ORDERED_COMMIT != 0 {
                spin_hint();
                old_status = self.status.load(Ordering::Relaxed);
            }

            tracing::event!(
                name: "work_item::cancel_toolate_spin_done",
                Level::TRACE,
                work = ?UsizePtr::from(self)
            );
        } else if old_status & WORK_STATUS_DOING_CANCEL != 0 {
            // somebody else is trying to do a cancel, so we don't do anything

            tracing::event!(
                name: "work_item::cancel_duplicate",
                Level::TRACE,
                work = ?UsizePtr::from(self)
            );
        } else {
            // we are doing the cancel

            tracing::event!(
                name: "work_item::cancel",
                Level::TRACE,
                work = ?UsizePtr::from(self)
            );

            // add the work item which we canceled to a list, so that
            // all of its locks can be dropped. this needs to happen with
            // the bucket lock *NOT* held, which is why it can't be done now
            q.add_work(self);
        }
    }

    /* Lock setup */

    /// returns (old_status, index, lock) of newly-set-up lock
    fn set_up_next_lock(
        &'work_item self,
        obj: NetlistRef<'arena>,
    ) -> Option<(
        u64,
        usize,
        &'work_item mut LockAndStroadData<
            'arena,
            'work_item,
            WorkItemPerLockData<'arena, 'work_item>,
        >,
    )> {
        let old_status = self.status.load(Ordering::Relaxed);
        if old_status & WORK_STATUS_DOING_CANCEL != 0 {
            return None;
        }

        let lock_idx = old_status & WORK_STATUS_NUM_LOCKS_MASK;
        if lock_idx == MAX_LOCKS_PER_WORK_ITEM as u64 {
            todo!("need to allocate a spill block?");
        }
        // self.locks_used.set(lock_idx + 1);
        let ret = unsafe {
            // this can only write to the thing @ lock_idx
            // (i.e. cannot data race with a cancel on another thread which can only access up to and *not* including lock_idx)
            let lock_ptr = (*self.locks[lock_idx as usize].as_ptr()).get();
            LockAndStroadData::init(lock_ptr, obj.type_erase());
            let inner_payload = LockAndStroadData::unsafe_stroad_work_item_link_ptr(lock_ptr);
            // lifetimes should've made it s.t. this is pinned in place
            (*inner_payload).w = self;
            (old_status, lock_idx as usize, &mut *lock_ptr)
        };

        tracing::event!(
            name: "work_item::next_lock",
            Level::TRACE,
            lock_idx,
        );

        Some(ret)
    }

    fn commit_unordered_lock(&self, old_status: u64, lock_idx: usize) {
        let new_status = (old_status & !WORK_STATUS_NUM_LOCKS_MASK) + lock_idx as u64 + 1;
        // can just write, cancel cannot happen
        self.status.store(new_status, Ordering::Relaxed);
    }

    /// if canceled, *this* thread has to release the just-acquired lock
    /// (other threads can't see it)
    fn commit_ordered_lock(&self, old_status: u64, lock_idx: usize) -> Result<(), ()> {
        let new_status = (old_status & !WORK_STATUS_NUM_LOCKS_MASK) + lock_idx as u64 + 1;
        // need release ordering to synchronize-with an acquire in the cancel code path
        if let Err(err_status) = self.status.compare_exchange(
            old_status,
            new_status,
            Ordering::Release,
            Ordering::Relaxed,
        ) {
            // raced with cancel and lost
            debug_assert!(err_status & WORK_STATUS_DOING_CANCEL != 0);
            Err(())
        } else {
            Ok(())
        }
    }

    /* Find lock, for RW phase */

    fn find_lock<C: FnOnce(LockState) -> bool>(
        &self,
        obj: TypeErasedObjRef<'arena>,
        check_state: C,
        rw: bool,
    ) -> usize {
        let status = self.status.load(Ordering::Relaxed);
        let num_locks = status & WORK_STATUS_NUM_LOCKS_MASK;
        // once we've started work, cancel is not allowed
        debug_assert!(status & WORK_STATUS_DOING_CANCEL == 0);

        // xxx can this be done more efficiently?
        for lock_idx in 0..num_locks as usize {
            let lock_i = unsafe { &*self.locks[lock_idx].assume_init_ref().get() };
            if lock_i.target() == obj {
                if !check_state(lock_i.state.get()) {
                    panic!("Tried to access a node in the wrong state")
                }

                if rw {
                    if lock_i.rw_handed_out.get() || lock_i.ro_handed_out.get() {
                        panic!("Tried to get RW guard, but guards already handed out");
                    }
                    lock_i.rw_handed_out.set(true);
                } else {
                    if lock_i.rw_handed_out.get() {
                        panic!("Tried to get RO guard, but RW guard already handed out");
                    }
                    lock_i.ro_handed_out.set(true);
                }

                return lock_idx;
            }
        }
        panic!("Tried to access a node that wasn't tagged in phase 1")
    }

    /* Algo-related stuff */

    /// after this work item pops back out after unparking, reset everything so that it's ready to try again
    ///
    /// it is only safe to call this if there's no chance this item is shared or has any locks used
    fn reset_state(&self) {
        self.status.store(0, Ordering::Relaxed);
    }

    fn drop_all_unordered_locks(
        &self,
        stroad: &Stroad<'arena, 'arena, WorkItemPerLockData<'arena, 'work_item>>,
        q: &mut work_queue::LocalQueue<&'arena WorkItem<'arena, 'arena>>,
    ) {
        let locks_used =
            (self.status.load(Ordering::Relaxed) & WORK_STATUS_NUM_LOCKS_MASK) as usize;
        unsafe {
            // release all the locks, as we failed to speculative grab what we needed
            for lock_idx in 0..locks_used {
                let lock = &*self.locks[lock_idx].assume_init_ref().get();
                debug_assert!(
                    lock.state.get() == LockState::LockedForUnorderedRead
                        || lock.state.get() == LockState::LockedForUnorderedWrite
                );
                lock.unlock(stroad, q);
            }
        }
    }

    fn drop_all_ordered_locks(
        &self,
        stroad: &Stroad<'arena, 'arena, WorkItemPerLockData<'arena, 'work_item>>,
        mut q: &ordered_commit_queue::OrderedCommitQueue<&'arena WorkItem<'arena, 'arena>>,
    ) {
        let mut old_status = self.status.load(Ordering::Relaxed);

        loop {
            let locks_used = old_status & WORK_STATUS_NUM_LOCKS_MASK;
            if locks_used == 0 {
                return;
            }

            let new_status = (old_status & !WORK_STATUS_NUM_LOCKS_MASK) + locks_used - 1;
            match self.status.compare_exchange_weak(
                old_status,
                new_status,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    // successfully decremented by 1, meaning we "own" the one at index locks_used - 1
                    let lock_idx = (locks_used - 1) as usize;
                    unsafe {
                        let lock = &*self.locks[lock_idx].assume_init_ref().get();
                        debug_assert!(
                            lock.state.get() == LockState::NewlyAllocatedOrdered
                                || lock.state.get() == LockState::LockedForOrderedRead
                                || lock.state.get() == LockState::LockedForOrderedWrite
                        );
                        lock.unlock(stroad, &mut q);
                    }

                    old_status = new_status;
                }
                Err(x) => old_status = x,
            }
        }
    }
}
#[derive(Debug)]
pub(crate) struct WorkItemPerLockData<'arena, 'work_item> {
    pub(crate) w: &'work_item WorkItem<'arena, 'work_item>,
}
impl<'arena, 'work_item> WorkItemInterface for WorkItemPerLockData<'arena, 'work_item> {
    type WorkItemTy = &'work_item WorkItem<'arena, 'work_item>;
    fn unpark<Q: WorkQueueInterface<WorkItemTy = Self::WorkItemTy>>(&self, onto_q: &mut Q) {
        self.w.unpark(onto_q)
    }
    fn cancel<Q: WorkQueueInterface<WorkItemTy = Self::WorkItemTy>>(&self, onto_q: &mut Q) {
        self.w.cancel(onto_q)
    }
}

/// Abstraction over ordered/unordered work queues
pub trait WorkQueueInterface {
    type WorkItemTy;
    fn add_work(&mut self, work_item: Self::WorkItemTy);
}

/// Top-level netlist + work items unified data structure
///
/// This doesn't actually *have* to be unified, but it's simpler this way
#[derive(Debug)]
pub struct NetlistManager<'arena> {
    heap: SlabRoot<'arena, NetlistTypeMapper>,
    stroad: Box<Stroad<'arena, 'arena, WorkItemPerLockData<'arena, 'arena>>>,
    /// Ensure that this isn't Sync (only various sub-accessors are),
    /// and that only one algorithm can be running at once
    in_use: Cell<bool>,
}
impl<'arena> NetlistManager<'arena> {
    /// Construct a new unified data structure
    pub fn new() -> Self {
        Self {
            heap: SlabRoot::new(),
            stroad: Stroad::new(),
            in_use: Cell::new(false),
        }
    }

    pub fn access_single_threaded(&'arena self) -> SingleThreadedView<'arena> {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        SingleThreadedView {
            x: self,
            heap_thread_shard: self.heap.new_thread(),
        }
    }

    pub fn run_unordered_algorithm<A: UnorderedAlgorithm>(
        &'arena self,
        algo: &A,
        queue: &work_queue::Queue<&'arena WorkItem<'arena, 'arena>>,
    ) {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        thread::scope(|s| {
            for (thread_i, local_queue) in queue.local_queues().enumerate() {
                let heap_thread_shard = self.heap.new_thread();
                let stroad = &self.stroad;
                s.spawn(move || {
                    let tracing_span =
                        tracing::span!(Level::TRACE, "unordered_algo::thread", thread_i);
                    let _span_enter = tracing_span.enter();
                    tracing::event!(
                        Level::TRACE,
                        thread_i,
                        heap_tid = heap_thread_shard.tid
                    );

                    // FIXME: this should be entirely unnecessary
                    let local_queue_rc = Rc::new(RefCell::new(local_queue));
                    let mut ro_view = UnorderedAlgorithmROView {
                        stroad,
                        heap_thread_shard,
                    };
                    while let Some(work_item) = {
                        let mut q = local_queue_rc.borrow_mut();
                        let work_item = q.pop();
                        drop(q);
                        work_item
                    } {
                        let work_span = tracing::span!(Level::TRACE, "unordered_algo::thread::work_item", attempted_work = ?UsizePtr::from(work_item));
                        let _work_span_enter = work_span.enter();

                        work_item.reset_state();
                        let ro_ret = algo.try_process_readonly(&mut ro_view, work_item);
                        if ro_ret.is_err() {
                            tracing::event!(
                                Level::TRACE,
                                "parked"
                            );

                            work_item.drop_all_unordered_locks(stroad, &mut local_queue_rc.borrow_mut());

                            let old_status = work_item.status.fetch_or(WORK_STATUS_FINISHED_PARKING, Ordering::Relaxed);
                            if old_status & WORK_STATUS_UNPARK_TRIGGERED != 0 {
                                // an unpark happened already while we were trying to release locks
                                let local_queue = &mut local_queue_rc.borrow_mut();
                                tracing::event!(
                                    Level::TRACE,
                                    "unparked before we finished parking"
                                );
                                local_queue.push(work_item);
                            } else {
                                // just park, don't do anything
                                // println!("parked!");
                            }

                            continue;
                        }
                        let ro_ret = ro_ret.unwrap();
                        tracing::event!(
                            Level::TRACE,
                            "RO phase completed successfully!"
                        );

                        let heap_thread_shard = {
                            let mut rw_view = UnorderedAlgorithmRWView {
                                heap_thread_shard: ro_view.heap_thread_shard,
                                queue: &mut local_queue_rc.borrow_mut(),
                            };
                            algo.process_finish_readwrite(&mut rw_view, work_item, ro_ret);
                            rw_view.heap_thread_shard
                        };

                        // release *all* locks, even if the RW phase didn't use one
                        work_item.drop_all_unordered_locks(stroad, &mut local_queue_rc.borrow_mut());

                        tracing::event!(
                            Level::TRACE,
                            "RW phase completed successfully!"
                        );
                        ro_view = UnorderedAlgorithmROView {
                            stroad,
                            heap_thread_shard,
                        };
                    }
                });
            }
        });
        // self.stroad._debug_dump();
        self.in_use.set(false);
    }

    pub fn run_ordered_algorithm<A: OrderedAlgorithm>(
        &'arena self,
        algo: &A,
        mut queue: &ordered_commit_queue::OrderedCommitQueue<&'arena WorkItem<'arena, 'arena>>,
        num_threads: usize,
    ) {
        assert!(num_threads <= ordered_commit_queue::MAX_THREADS);
        assert!(!self.in_use.get());
        self.in_use.set(true);

        thread::scope(|s| {
            for thread_i in 0..num_threads {
                let heap_thread_shard = self.heap.new_thread();
                let stroad = &self.stroad;
                s.spawn(move || {
                    let tracing_span =
                        tracing::span!(Level::TRACE, "ordered_algo::thread", thread_i);
                    let _span_enter = tracing_span.enter();

                    let mut ro_view = OrderedAlgorithmROView {
                        stroad,
                        unpark_q: queue,
                        cancel_list: Vec::new(),
                        heap_thread_shard,
                    };
                    while let Some(work_item_with_prio) = queue.get_some_work(thread_i) {
                        let ItemWithPriority {
                            item: work_item,
                            prio: work_prio,
                        } = work_item_with_prio;
                        let item_status = work_item.status.load(Ordering::Relaxed);

                        let work_span = tracing::span!(
                            Level::TRACE,
                            "ordered_algo::thread::work_item",
                            attempted_work.item = ?UsizePtr::from(work_item),
                            attempted_work.status = item_status,
                            attempted_work.prio = work_prio,
                        );
                        let _work_span_enter = work_span.enter();

                        if item_status & WORK_STATUS_GRABBED_LOCKS == 0 {
                            // need to speculatively grab work
                            work_item.reset_state();
                            let ro_ret = algo.try_process_readonly(&mut ro_view, work_item);
                            for cancel in ro_view.cancel_list.iter() {
                                // FIXME completely untested
                                cancel.drop_all_ordered_locks(stroad, queue);
                            }
                            if let Err(e) = ro_ret {
                                match e {
                                    SpeculativeLockGrabResult::Block => {
                                        tracing::event!(
                                            name: "ordered_algo::park",
                                            Level::TRACE,
                                            "parked"
                                        );

                                        work_item.drop_all_ordered_locks(stroad, queue);

                                        let old_status = work_item.status.fetch_or(
                                            WORK_STATUS_FINISHED_PARKING,
                                            Ordering::Relaxed,
                                        );
                                        if old_status & WORK_STATUS_UNPARK_TRIGGERED != 0 {
                                            // an unpark happened already while we were trying to release locks
                                            tracing::event!(
                                                name: "ordered_algo::unpark_tooearly_recovery",
                                                Level::TRACE,
                                                "unparked before we finished parking"
                                            );
                                            queue.add_work(work_item);
                                        } else {
                                            // just park, don't do anything
                                            // println!("parked!");
                                        }
                                    }
                                    SpeculativeLockGrabResult::Cancel => {
                                        tracing::event!(
                                            name: "ordered_algo::cancelled_during_ro",
                                            Level::TRACE,
                                            "cancelled during RO phase"
                                        );

                                        work_item.drop_all_ordered_locks(stroad, queue);
                                        queue.add_work(work_item);
                                    }
                                }

                                continue;
                            } else {
                                tracing::event!(
                                    name: "ordered_algo::ro_done",
                                    Level::TRACE,
                                    "RO phase completed successfully!"
                                );

                                let _status = work_item
                                    .status
                                    .fetch_or(WORK_STATUS_GRABBED_LOCKS, Ordering::Relaxed);
                            }
                        }

                        if work_item.prio <= queue.commit_priority() as u64 {
                            // can attempt RW phase

                            let old_status = work_item.status.fetch_update(
                                Ordering::Relaxed,
                                Ordering::Relaxed,
                                |x| {
                                    if x & WORK_STATUS_DOING_CANCEL != 0 {
                                        None
                                    } else {
                                        Some(x | WORK_STATUS_DOING_ORDERED_COMMIT)
                                    }
                                },
                            );

                            if old_status.is_err() {
                                tracing::event!(
                                    name: "ordered_algo::cancelled_starting_rw",
                                    Level::TRACE,
                                    "cancelled during RW phase start"
                                );

                                work_item.drop_all_ordered_locks(stroad, queue);
                                queue.add_work(work_item);
                            }

                            // RW phase is committed to go ahead

                            let heap_thread_shard = {
                                let mut rw_view = OrderedAlgorithmRWView {
                                    heap_thread_shard: ro_view.heap_thread_shard,
                                    queue,
                                };
                                algo.process_finish_readwrite(&mut rw_view, work_item);
                                rw_view.heap_thread_shard
                            };

                            // release *all* locks, even if the RW phase didn't use one
                            work_item.drop_all_ordered_locks(stroad, queue);

                            tracing::event!(
                                name: "ordered_algo::rw_done",
                                Level::TRACE,
                                "RW phase completed successfully!"
                            );
                            ro_view = OrderedAlgorithmROView {
                                stroad,
                                unpark_q: queue,
                                cancel_list: Vec::new(),
                                heap_thread_shard,
                            };

                            queue.finish_work(
                                thread_i,
                                ItemWithPriority {
                                    item: work_item,
                                    prio: work_prio,
                                },
                            );
                        } else {
                            // cannot attempt RW phase
                            tracing::event!(
                                name: "ordered_algo::not_at_head",
                                Level::TRACE,
                                "cannot commit; not at head of priority queue"
                            );

                            queue.put_back_waiting_item(
                                thread_i,
                                ItemWithPriority {
                                    item: work_item,
                                    prio: work_prio,
                                },
                            )
                        }
                    }
                });
            }
        });
        // self.stroad._debug_dump();
        self.in_use.set(false);
    }
}
