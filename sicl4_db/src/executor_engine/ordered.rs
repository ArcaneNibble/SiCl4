//! This module contains code to support operations where the order *does* matter.
//!
//! In other words, the "fringe" of the graph algorithm is a priority queue.

// FIXME MASSIVE CODE DUPLICATION

use std::mem;

use ordered_commit_queue::ItemWithPriority;

use crate::allocator::SlabThreadShard;
use crate::lock_ops::*;

use super::*;

pub trait OrderedAlgorithm: Send + Sync {
    fn try_process_readonly<'algo_global_state, 'view, 'arena, 'q>(
        &'algo_global_state self,
        view: &'view mut OrderedAlgorithmROView<'arena, 'q>,
        work_item: &'arena WorkItem<'arena, 'arena>,
    ) -> Result<(), SpeculativeLockGrabResult>;

    fn process_finish_readwrite<'algo_state, 'view, 'arena, 'q>(
        &'algo_state self,
        view: &'view mut OrderedAlgorithmRWView<'arena, 'q>,
        work_item: &'arena WorkItem<'arena, 'arena>,
    );
}

#[derive(Debug)]
pub struct OrderedAlgorithmROView<'arena, 'q> {
    pub(super) stroad: &'arena Stroad<'arena, 'arena, WorkItemPerLockData<'arena, 'arena>>,
    pub(super) unpark_q:
        &'q ordered_commit_queue::OrderedCommitQueue<&'arena WorkItem<'arena, 'arena>>,
    pub(super) cancel_list: Vec<&'arena WorkItem<'arena, 'arena>>,
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
}
impl<'arena, 'q> NetlistROView<'arena> for OrderedAlgorithmROView<'arena, 'q> {
    fn try_lock_cell<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
        want_write: bool,
    ) -> Result<Option<ROGuard<'arena, NetlistCell<'arena>>>, SpeculativeLockGrabResult> {
        let (old_status, lock_idx, lock) = work_item
            .set_up_next_lock(NetlistRef::Cell(obj))
            .ok_or(SpeculativeLockGrabResult::Cancel)?;
        let lock_gotten = if !want_write {
            lock.ordered_try_read(self.stroad, work_item.prio, &mut self.cancel_list)
        } else {
            lock.ordered_try_write(self.stroad, work_item.prio, &mut self.cancel_list)
        };
        if work_item.commit_ordered_lock(old_status, lock_idx).is_err() {
            // *sigh*, canceled just as we grabbed this lock
            unsafe { lock.unlock(self.stroad, &mut self.unpark_q) };
            return Err(SpeculativeLockGrabResult::Cancel);
        }
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
        let (old_status, lock_idx, lock) = work_item
            .set_up_next_lock(NetlistRef::Wire(obj))
            .ok_or(SpeculativeLockGrabResult::Cancel)?;
        let lock_gotten = if !want_write {
            lock.ordered_try_read(self.stroad, work_item.prio, &mut self.cancel_list)
        } else {
            lock.ordered_try_write(self.stroad, work_item.prio, &mut self.cancel_list)
        };
        if work_item.commit_ordered_lock(old_status, lock_idx).is_err() {
            // *sigh*, canceled just as we grabbed this lock
            unsafe { lock.unlock(self.stroad, &mut self.unpark_q) };
            return Err(SpeculativeLockGrabResult::Cancel);
        }
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
pub struct OrderedAlgorithmRWView<'arena, 'q> {
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
    pub(super) queue:
        &'q ordered_commit_queue::OrderedCommitQueue<&'arena WorkItem<'arena, 'arena>>,
}
impl<'arena, 'q> NetlistRWView<'arena> for OrderedAlgorithmRWView<'arena, 'q> {
    fn new_cell<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
    ) -> RWGuard<'arena, NetlistCell<'arena>> {
        let (new, gen) = self
            .heap_thread_shard
            .allocate::<LockedObj<NetlistCell<'arena>>>();
        unsafe {
            LockedObj::init_ordered(new.as_mut_ptr(), gen);
            let _ = NetlistCell::init((*new.as_mut_ptr()).payload.get());
            let new_ref = ObjRef {
                ptr: new.assume_init_ref(),
                gen,
            };
            let (old_status, lock_idx, lock) = work_item
                .set_up_next_lock(NetlistRef::Cell(new_ref))
                .unwrap();
            lock.state.set(LockState::NewlyAllocatedOrdered);
            work_item.commit_ordered_lock(old_status, lock_idx).unwrap();
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
            LockedObj::init_ordered(new.as_mut_ptr(), gen);
            let _ = NetlistWire::init((*new.as_mut_ptr()).payload.get());
            let new_ref = ObjRef {
                ptr: new.assume_init_ref(),
                gen,
            };
            let (old_status, lock_idx, lock) = work_item
                .set_up_next_lock(NetlistRef::Wire(new_ref))
                .unwrap();
            lock.state.set(LockState::NewlyAllocatedOrdered);
            work_item.commit_ordered_lock(old_status, lock_idx).unwrap();
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
                LockState::LockedForOrderedRead | LockState::LockedForOrderedWrite => true,
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
                LockState::LockedForOrderedWrite => true,
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
                LockState::LockedForOrderedRead | LockState::LockedForOrderedWrite => true,
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
                LockState::LockedForOrderedWrite => true,
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
impl<'arena, 'q> OrderedAlgorithmRWView<'arena, 'q> {
    pub fn add_work<'wrapper>(&'wrapper mut self, node: NetlistRef<'arena>, prio: u64) {
        let work_item = self.allocate_new_work(node, prio);
        self.queue.add_work(work_item);
    }
}

impl<'arena, 'work_item> WorkQueueInterface
    for ordered_commit_queue::OrderedCommitQueue<&'work_item WorkItem<'arena, 'work_item>>
{
    type WorkItemTy = &'work_item WorkItem<'arena, 'work_item>;
    fn add_work(&mut self, work_item: &'work_item WorkItem<'arena, 'work_item>) {
        self.create_new_work(ItemWithPriority {
            item: work_item,
            prio: work_item.prio as i64,
        })
    }
}
impl<'q, 'arena, 'work_item> WorkQueueInterface
    for &'q ordered_commit_queue::OrderedCommitQueue<&'work_item WorkItem<'arena, 'work_item>>
{
    type WorkItemTy = &'work_item WorkItem<'arena, 'work_item>;
    fn add_work(&mut self, work_item: &'work_item WorkItem<'arena, 'work_item>) {
        self.create_new_work(ItemWithPriority {
            item: work_item,
            prio: work_item.prio as i64,
        })
    }
}

impl<'arena, 'work_item> WorkQueueInterface for Vec<&'work_item WorkItem<'arena, 'work_item>> {
    type WorkItemTy = &'work_item WorkItem<'arena, 'work_item>;
    fn add_work(&mut self, work_item: &'work_item WorkItem<'arena, 'work_item>) {
        self.push(work_item);
    }
}
