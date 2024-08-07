//! Code for controlling the running of algorithms against netlists

use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::sync::atomic::Ordering;
use std::{cell::Cell, fmt::Debug};

use netlist::*;
use single_threaded::SingleThreadedView;
use tracing::Level;

use crate::lock_ops::stroad::WorkItemInterface;
use crate::lock_ops::{LockAndStroadData, LockState, TypeErasedObjRef};
use crate::loom_testing::*;
use crate::netlist::*;
use crate::{allocator::SlabRoot, lock_ops::stroad::Stroad};

pub mod netlist;
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
        todo!()
    }

    fn cancel<Q: WorkQueueInterface<WorkItemTy = &'work_item Self>>(&'work_item self, q: &mut Q) {
        todo!()
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
}
