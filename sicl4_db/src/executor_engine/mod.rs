//! Code for controlling the running of algorithms against netlists

use std::marker::PhantomData;
use std::{cell::Cell, fmt::Debug};

use netlist::{NetlistRef, NetlistTypeMapper};
use single_threaded::SingleThreadedView;

use crate::lock_ops::stroad::WorkItemInterface;
use crate::{allocator::SlabRoot, lock_ops::stroad::Stroad};

pub mod netlist;
pub mod single_threaded;

// TODO
pub struct WorkItem<'arena, 'work_item> {
    seed_node: NetlistRef<'arena>,
    prio: u64,
    _pd: PhantomData<&'work_item ()>,
}
impl<'arena, 'work_item> Debug for WorkItem<'arena, 'work_item> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WorkItem")
            .field("seed_node", &self.seed_node)
            .field("prio", &self.prio)
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
        &mut *self_
    }

    fn unpark<Q: WorkQueueInterface<WorkItemTy = &'work_item Self>>(&'work_item self, q: &mut Q) {
        todo!()
    }

    fn cancel<Q: WorkQueueInterface<WorkItemTy = &'work_item Self>>(&'work_item self, q: &mut Q) {
        todo!()
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
