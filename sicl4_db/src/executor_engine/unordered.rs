//! This module contains code to support operations where the order does not matter.
//!
//! In other words, the "fringe" of the graph algorithm is an unordered set.

// FIXME there's a lot of code duplication here

use std::{mem, sync::atomic::Ordering};

use crate::allocator::SlabThreadShard;
use crate::lock_ops::*;
use crate::netlist::*;

use super::*;

pub trait UnorderedAlgorithm: Send + Sync {
    type ROtoRWTy;

    fn try_process_readonly<'algo_global_state, 'view, 'arena>(
        &'algo_global_state self,
        view: &'view mut UnorderedAlgorithmROView<'arena>,
        work_item: &'arena WorkItem<'arena, 'arena>,
    ) -> Result<Self::ROtoRWTy, SpeculativeLockGrabResult>;

    fn process_finish_readwrite<'algo_state, 'view, 'arena, 'q>(
        &'algo_state self,
        view: &'view mut UnorderedAlgorithmRWView<'arena, 'q>,
        work_item: &'arena WorkItem<'arena, 'arena>,
        ro_output: Self::ROtoRWTy,
    );
}

#[derive(Debug)]
pub struct UnorderedAlgorithmROView<'arena> {
    pub(super) stroad: &'arena Stroad<'arena, 'arena, WorkItemPerLockData<'arena, 'arena>>,
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
}
impl<'arena> NetlistROView<'arena> for UnorderedAlgorithmROView<'arena> {
    fn try_lock_cell<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
        want_write: bool,
    ) -> Result<Option<ROGuard<'arena, NetlistCell<'arena>>>, SpeculativeLockGrabResult> {
        let (old_status, lock_idx, lock) =
            work_item.set_up_next_lock(NetlistRef::Cell(obj)).unwrap();
        let lock_gotten = if !want_write {
            lock.unordered_try_read(self.stroad)
        } else {
            lock.unordered_try_write(self.stroad)
        };
        work_item.commit_unordered_lock(old_status, lock_idx);
        if let Ok(lock_gotten) = lock_gotten {
            if !lock_gotten {
                return Err(SpeculativeLockGrabResult::Block);
            }
            Ok(Some(ROGuard { x: obj }))
        } else {
            return Ok(None);
        }
    }

    fn try_lock_wire<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistWireRef<'arena>,
        want_write: bool,
    ) -> Result<Option<ROGuard<'arena, NetlistWire<'arena>>>, SpeculativeLockGrabResult> {
        let (old_status, lock_idx, lock) =
            work_item.set_up_next_lock(NetlistRef::Wire(obj)).unwrap();
        let lock_gotten = if !want_write {
            lock.unordered_try_read(self.stroad)
        } else {
            lock.unordered_try_write(self.stroad)
        };
        work_item.commit_unordered_lock(old_status, lock_idx);
        if let Ok(lock_gotten) = lock_gotten {
            if !lock_gotten {
                return Err(SpeculativeLockGrabResult::Block);
            }
            Ok(Some(ROGuard { x: obj }))
        } else {
            return Ok(None);
        }
    }
}

#[derive(Debug)]
pub struct UnorderedAlgorithmRWView<'arena, 'q> {
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
    pub(super) queue: &'q mut work_queue::LocalQueue<&'arena WorkItem<'arena, 'arena>>,
}
impl<'arena, 'q> NetlistRWView<'arena> for UnorderedAlgorithmRWView<'arena, 'q> {
    fn new_cell<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
    ) -> RWGuard<'arena, NetlistCell<'arena>> {
        let (new, gen) = self
            .heap_thread_shard
            .allocate::<LockedObj<NetlistCell<'arena>>>();
        unsafe {
            LockedObj::init_unordered(new.as_mut_ptr(), gen);
            let _ = NetlistCell::init((*new.as_mut_ptr()).payload.get());
            let new_ref = ObjRef {
                ptr: new.assume_init_ref(),
                gen,
            };
            let (old_status, lock_idx, lock) = work_item
                .set_up_next_lock(NetlistRef::Cell(new_ref))
                .unwrap();
            lock.state.set(LockState::LockedForUnorderedWrite);
            work_item.commit_unordered_lock(old_status, lock_idx);
            RWGuard {
                x: new_ref,
                lock_idx,
            }
        }
    }
    fn new_wire<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
    ) -> RWGuard<'arena, NetlistWire<'arena>> {
        let (new, gen) = self
            .heap_thread_shard
            .allocate::<LockedObj<NetlistWire<'arena>>>();
        unsafe {
            LockedObj::init_unordered(new.as_mut_ptr(), gen);
            let _ = NetlistWire::init((*new.as_mut_ptr()).payload.get());
            let new_ref = ObjRef {
                ptr: new.assume_init_ref(),
                gen,
            };
            let (old_status, lock_idx, lock) = work_item
                .set_up_next_lock(NetlistRef::Wire(new_ref))
                .unwrap();
            lock.state.set(LockState::LockedForUnorderedWrite);
            work_item.commit_unordered_lock(old_status, lock_idx);
            RWGuard {
                x: new_ref,
                lock_idx,
            }
        }
    }

    fn delete_cell<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        guard: RWGuard<'arena, NetlistCell<'arena>>,
    ) {
        // FIXME THIS IS NOT TESTED
        let lock = unsafe { &*work_item.locks[guard.lock_idx].assume_init_ref().get() };
        lock.state.set(LockState::Unlocked);
        guard.x.ptr.lock_and_generation.store(0, Ordering::Relaxed);
        unsafe {
            // safety: the guard represents exclusive access to the node
            self.heap_thread_shard.free(guard.x.ptr)
        }
        mem::forget(guard);
    }
    fn delete_wire<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        guard: RWGuard<'arena, NetlistWire<'arena>>,
    ) {
        // FIXME THIS IS NOT TESTED
        let lock = unsafe { &*work_item.locks[guard.lock_idx].assume_init_ref().get() };
        lock.state.set(LockState::Unlocked);
        guard.x.ptr.lock_and_generation.store(0, Ordering::Relaxed);
        unsafe {
            // safety: the guard represents exclusive access to the node
            self.heap_thread_shard.free(guard.x.ptr)
        }
        mem::forget(guard);
    }

    fn get_cell_read<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
    ) -> ROGuard<'arena, NetlistCell<'arena>> {
        let _lock_idx = work_item.find_lock(
            obj.type_erase(),
            |state| match state {
                LockState::LockedForUnorderedRead | LockState::LockedForUnorderedWrite => true,
                _ => false,
            },
            false,
        );
        ROGuard { x: obj }
    }
    fn get_cell_write<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
    ) -> RWGuard<'arena, NetlistCell<'arena>> {
        let lock_idx = work_item.find_lock(
            obj.type_erase(),
            |state| match state {
                LockState::LockedForUnorderedWrite => true,
                _ => false,
            },
            true,
        );
        RWGuard { x: obj, lock_idx }
    }

    fn get_wire_read<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistWireRef<'arena>,
    ) -> ROGuard<'arena, NetlistWire<'arena>> {
        let _lock_idx = work_item.find_lock(
            obj.type_erase(),
            |state| match state {
                LockState::LockedForUnorderedRead | LockState::LockedForUnorderedWrite => true,
                _ => false,
            },
            false,
        );
        ROGuard { x: obj }
    }

    fn get_wire_write<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistWireRef<'arena>,
    ) -> RWGuard<'arena, NetlistWire<'arena>> {
        let lock_idx = work_item.find_lock(
            obj.type_erase(),
            |state| match state {
                LockState::LockedForUnorderedWrite => true,
                _ => false,
            },
            true,
        );
        RWGuard { x: obj, lock_idx }
    }

    fn allocate_new_work<'wrapper>(
        &'wrapper mut self,
        node: NetlistRef<'arena>,
        prio: u64,
    ) -> &'arena mut WorkItem<'arena, 'arena> {
        assert!(prio < i64::MAX as u64);
        let (new, _gen) = self.heap_thread_shard.allocate::<WorkItem>();
        let work_item = unsafe { WorkItem::init(new.as_mut_ptr(), node, prio) };
        work_item
    }
}
impl<'arena, 'q> UnorderedAlgorithmRWView<'arena, 'q> {
    pub fn add_work<'wrapper>(&'wrapper mut self, node: NetlistRef<'arena>) {
        let work_item = self.allocate_new_work(node, 0);
        self.queue.push(&*work_item);
    }
}

impl<'arena, 'work_item> WorkQueueInterface
    for work_queue::LocalQueue<&'work_item WorkItem<'arena, 'work_item>>
{
    type WorkItemTy = &'work_item WorkItem<'arena, 'work_item>;
    fn add_work(&mut self, work_item: &'work_item WorkItem<'arena, 'work_item>) {
        self.push(work_item);
    }
}
impl<'arena, 'work_item> WorkQueueInterface
    for work_queue::Queue<&'work_item WorkItem<'arena, 'work_item>>
{
    type WorkItemTy = &'work_item WorkItem<'arena, 'work_item>;
    fn add_work(&mut self, work_item: &'work_item WorkItem<'arena, 'work_item>) {
        self.push(work_item);
    }
}
impl<'q, 'arena, 'work_item> WorkQueueInterface
    for &'q work_queue::Queue<&'work_item WorkItem<'arena, 'work_item>>
{
    type WorkItemTy = &'work_item WorkItem<'arena, 'work_item>;
    fn add_work(&mut self, work_item: &'work_item WorkItem<'arena, 'work_item>) {
        self.push(work_item);
    }
}
