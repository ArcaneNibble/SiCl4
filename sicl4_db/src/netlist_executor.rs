//! Manages a netlist and running algorithms on it

use std::{alloc::Layout, mem::MaybeUninit, thread};

use crate::{allocator::*, locking::*, netlist::*, stroad::*};

pub trait UnorderedAlgorithm {
    fn process_node<'algo_state, 'arena>(
        &'algo_state self,
        node: NetlistRef<'arena>,
    ) -> Result<(), ()>;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum NetlistRef<'arena> {
    Cell(NetlistCellRef<'arena>),
    Wire(NetlistWireRef<'arena>),
}
impl<'arena> From<NetlistCellRef<'arena>> for NetlistRef<'arena> {
    fn from(value: NetlistCellRef<'arena>) -> Self {
        Self::Cell(value)
    }
}
impl<'arena> From<NetlistWireRef<'arena>> for NetlistRef<'arena> {
    fn from(value: NetlistWireRef<'arena>) -> Self {
        Self::Wire(value)
    }
}

const NUM_THREADS_FOR_NOW: usize = 1;
const MAX_ORDERED_LOCKS_PER_WORK_ITEM: usize = 4;

struct WorkItemPayload<'arena, 'work_item> {
    w: &'work_item WorkItem<'arena, 'work_item>,
}
impl<'arena, 'work_item> LockInstPayload for WorkItemPayload<'arena, 'work_item> {
    fn cancel<'lock_inst, K>(e: &'lock_inst mut LockInstance<'lock_inst, K, Self>)
    where
        Self: Sized,
    {
        todo!()
    }

    fn unpark<'lock_inst, K>(e: &'lock_inst mut LockInstance<'lock_inst, K, Self>)
    where
        Self: Sized,
    {
        todo!()
    }
}

#[derive(Debug)]
pub struct WorkItem<'arena, 'work_item> {
    seed_node: NetlistRef<'arena>,
    locks: [MaybeUninit<
        RWLock<'arena, 'work_item, NetlistRef<'arena>, WorkItemPayload<'arena, 'work_item>>,
    >; MAX_ORDERED_LOCKS_PER_WORK_ITEM],
}
// xxx fixme wtf is this
unsafe impl<'arena, 'work_item> Sync for WorkItem<'arena, 'work_item> {}
impl<'arena, 'work_item> WorkItem<'arena, 'work_item> {
    pub unsafe fn init(self_: *mut Self, node: NetlistRef<'arena>) -> &'work_item mut Self {
        (*self_).seed_node = node;
        &mut *self_
    }
}

/// Top-level netlist + work items unified data structure
///
/// This doesn't actually *have* to be unified, but it's simpler this way
#[derive(Debug)]
pub struct NetlistManager<'arena> {
    heap: SlabRoot<'arena, NetlistTypeMapper>,
    stroad: Box<Stroad<'arena, NetlistRef<'arena>, WorkItemPayload<'arena, 'arena>>>,
}
impl<'arena> NetlistManager<'arena> {
    /// Construct a new unified data structure
    pub fn new() -> Self {
        Self {
            heap: SlabRoot::new(),
            stroad: Stroad::new(),
        }
    }

    pub fn run_unordered_algorithm<A: UnorderedAlgorithm>(&'arena self, algo: A) {
        thread::scope(|s| {
            for _ in 0..NUM_THREADS_FOR_NOW {
                s.spawn(move || {
                    let thread_heap_shard = self.heap.new_thread();
                });
            }
        })
    }

    /// Get a thread shard for performing operations on the netlist
    pub fn new_thread(&'arena self) -> NetlistManagerThread<'arena> {
        NetlistManagerThread {
            heap_shard: self.heap.new_thread(),
            stroad: &self.stroad,
        }
    }
}

/// Separate cells/wires/work items into separate type bins
struct NetlistTypeMapper {}
impl TypeMapper for NetlistTypeMapper {
    type BinsArrayTy<T> = [T; 3];
    const LAYOUTS: &'static [&'static [Layout]] = &[
        &[Layout::new::<LockedObj<NetlistCell>>()],
        &[Layout::new::<LockedObj<NetlistWire>>()],
        &[Layout::new::<WorkItem>()],
    ];
}
impl<'arena> TypeMappable<NetlistTypeMapper> for LockedObj<NetlistCell<'arena>> {
    const I: usize = 0;
}
impl<'arena> TypeMappable<NetlistTypeMapper> for LockedObj<NetlistWire<'arena>> {
    const I: usize = 1;
}
impl<'arena, 'work_item> TypeMappable<NetlistTypeMapper> for WorkItem<'arena, 'work_item> {
    const I: usize = 2;
}

/// Provides one thread with access to the netlist
#[derive(Debug)]
pub struct NetlistManagerThread<'arena> {
    heap_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
    stroad: &'arena Stroad<'arena, NetlistRef<'arena>, WorkItemPayload<'arena, 'arena>>,
}

impl<'arena> NetlistManagerThread<'arena> {
    pub fn new_work_item<'wrapper>(
        &'wrapper self,
        node: NetlistRef<'arena>,
    ) -> &'arena mut WorkItem<'arena, 'arena> {
        let (new, _gen) = self.heap_shard.allocate::<WorkItem>();
        unsafe { WorkItem::init(new.as_mut_ptr(), node) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn executor_ensure_obj_safety() {
        let _x: &dyn UnorderedAlgorithm;
    }

    #[cfg(not(loom))]
    #[test]
    fn executor_asdf() {
        let all_the_stuff = NetlistManager::new();
        // dbg!(&all_the_stuff);
        let thread_shard = all_the_stuff.new_thread();
        // dbg!(&thread_shard);

        // let work = thread_shard.new_work_item();
        // dbg!(work);
    }
}
