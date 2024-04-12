//! Manages a netlist and running algorithms on it

use std::{
    alloc::Layout,
    cell::{Cell, UnsafeCell},
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    sync::atomic::Ordering,
    thread,
};

use crate::allocator::*;
use crate::lock_ops::*;
use crate::loom_testing::*;
use crate::netlist::*;
use crate::stroad::*;

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
impl<'arena> NetlistRef<'arena> {
    fn type_erase(self) -> TypeErasedObjRef<'arena> {
        match self {
            NetlistRef::Cell(x) => x.type_erase(),
            NetlistRef::Wire(x) => x.type_erase(),
        }
    }
}

const MAX_LOCKS_PER_WORK_ITEM: usize = 4;

#[derive(Debug)]
struct WorkItemPerLockData<'arena, 'work_item> {
    w: &'work_item WorkItem<'arena, 'work_item>,
    guard_handed_out: AtomicBool,
}
impl<'arena, 'work_item> StroadToWorkItemLink for WorkItemPerLockData<'arena, 'work_item> {
    fn cancel(&self) {
        self.w.cancel()
    }

    fn unpark(&self) {
        self.w.unpark()
    }
}

#[derive(Debug)]
pub struct WorkItem<'arena, 'work_item> {
    seed_node: NetlistRef<'arena>,
    locks_used: Cell<usize>,
    locks: [MaybeUninit<
        UnsafeCell<LockAndStroadData<'arena, 'work_item, WorkItemPerLockData<'arena, 'work_item>>>,
    >; MAX_LOCKS_PER_WORK_ITEM],
}
// xxx fixme wtf is this
// xxx fixme the entire safety of this needs to be figured out, since it has unsafe inner mutability
unsafe impl<'arena, 'work_item> Send for WorkItem<'arena, 'work_item> {}
unsafe impl<'arena, 'work_item> Sync for WorkItem<'arena, 'work_item> {}
impl<'arena, 'work_item> WorkItem<'arena, 'work_item> {
    pub unsafe fn init(self_: *mut Self, node: NetlistRef<'arena>) -> &'work_item mut Self {
        (*self_).seed_node = node;
        (*self_).locks_used = Cell::new(0);
        &mut *self_
    }

    fn unpark(&'work_item self) {
        todo!()
    }

    fn cancel(&'work_item self) {
        todo!()
    }

    fn next_lock(
        &'work_item self,
        obj: NetlistRef<'arena>,
    ) -> (
        usize,
        &'work_item mut LockAndStroadData<
            'arena,
            'work_item,
            WorkItemPerLockData<'arena, 'work_item>,
        >,
    ) {
        let lock_idx = self.locks_used.get();
        if lock_idx == MAX_LOCKS_PER_WORK_ITEM {
            todo!("need to allocate a spill block?");
        }
        self.locks_used.set(lock_idx + 1);
        unsafe {
            let lock_ptr = (*self.locks[lock_idx].as_ptr()).get();
            LockAndStroadData::init(lock_ptr, obj.type_erase());
            let inner_payload = LockAndStroadData::unsafe_stroad_work_item_link_ptr(lock_ptr);
            // lifetimes should've made it s.t. this is pinned in place
            (*inner_payload).w = self;
            (*inner_payload).guard_handed_out = AtomicBool::new(false);
            (lock_idx, &mut *lock_ptr)
        }
    }
}

/// Top-level netlist + work items unified data structure
///
/// This doesn't actually *have* to be unified, but it's simpler this way
#[derive(Debug)]
pub struct NetlistManager<'arena> {
    heap: SlabRoot<'arena, NetlistTypeMapper>,
    stroad: Box<Stroad<'arena, TypeErasedObjRef<'arena>, WorkItemPerLockData<'arena, 'arena>>>,
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
        queue: &work_queue::Queue<&'arena mut WorkItem<'arena, 'arena>>,
    ) {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        thread::scope(|s| {
            for mut local_queue in queue.local_queues() {
                let heap_thread_shard = self.heap.new_thread();
                let stroad = &self.stroad;
                s.spawn(move || {
                    let mut ro_view = UnorderedAlgorithmROView {
                        stroad,
                        heap_thread_shard,
                    };
                    while let Some(work_item) = local_queue.pop() {
                        // we are passed in exclusive pointers, but, as soon as any locks are created,
                        // the reference is no longer &mut exclusive. downgrade immediately.
                        // fixme should we just never expose &mut WorkItem?
                        let work_item = &*work_item;
                        let seed_node = work_item.seed_node;
                        let ro_ret = algo.try_process_readonly(&mut ro_view, seed_node, work_item);
                        if ro_ret.is_err() {
                            println!("parked!");
                            unsafe {
                                let locks_used = work_item.locks_used.get();
                                let lock_that_failed =
                                    &*work_item.locks[locks_used - 1].assume_init_ref().get();
                                debug_assert!(lock_that_failed.state.get() == LockState::Parked);

                                // release all the other locks, as we failed to speculative grab what we needed
                                for lock_idx in 0..(locks_used - 1) {
                                    let lock = &*work_item.locks[lock_idx].assume_init_ref().get();
                                    debug_assert!(
                                        (lock.state.get() == LockState::LockedForUnorderedRead)
                                            || lock.state.get()
                                                == LockState::LockedForUnorderedWrite
                                    );
                                    lock.unlock(stroad);
                                }
                            }
                            continue;
                        }
                        let ro_ret = ro_ret.unwrap();

                        let mut rw_view = UnorderedAlgorithmRWView {
                            stroad,
                            heap_thread_shard: ro_view.heap_thread_shard,
                        };
                        algo.process_finish_readwrite(&mut rw_view, seed_node, work_item, ro_ret);
                        ro_view = UnorderedAlgorithmROView {
                            stroad,
                            heap_thread_shard: rw_view.heap_thread_shard,
                        };
                    }
                });
            }
        });
        self.in_use.set(false);
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

mod single_threaded;
pub use single_threaded::*;

mod unordered;
pub use unordered::*;

#[cfg(test)]
mod tests;
