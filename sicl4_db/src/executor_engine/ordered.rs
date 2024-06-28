//! This module contains code to support operations where the order *does* matter.
//!
//! In other words, the "fringe" of the graph algorithm is a priority queue.

// FIXME MASSIVE CODE DUPLICATION

use super::*;

pub trait OrderedAlgorithm: Send + Sync {
    type ROtoRWTy;

    fn try_process_readonly<'algo_global_state, 'view, 'arena>(
        &'algo_global_state self,
        view: &'view mut OrderedAlgorithmROView<'arena>,
        work_item: &'arena WorkItem<'arena, 'arena>,
    ) -> Result<Self::ROtoRWTy, ()>;

    fn process_finish_readwrite<'algo_state, 'view, 'arena, 'q>(
        &'algo_state self,
        view: &'view mut OrderedAlgorithmRWView<'arena, 'q>,
        work_item: &'arena WorkItem<'arena, 'arena>,
        ro_output: Self::ROtoRWTy,
    );
}

#[derive(Debug)]
pub struct OrderedAlgorithmROView<'arena> {
    pub(super) stroad:
        &'arena Stroad<'arena, TypeErasedObjRef<'arena>, WorkItemPerLockData<'arena, 'arena>>,
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
}
impl<'arena> OrderedAlgorithmROView<'arena> {
    pub fn try_lock_cell<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
        want_write: bool,
    ) -> Result<ROGuard<'arena, NetlistCell<'arena>>, ()> {
        let (_lock_idx, lock) = work_item.next_lock(NetlistRef::Cell(obj));
        let lock_gotten = if !want_write {
            lock.ordered_try_read(self.stroad, work_item.prio)?
        } else {
            lock.ordered_try_write(self.stroad, work_item.prio)?
        };
        if !lock_gotten {
            return Err(());
        }
        Ok(ROGuard { x: obj })
    }

    pub fn try_lock_wire<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistWireRef<'arena>,
        want_write: bool,
    ) -> Result<ROGuard<'arena, NetlistWire<'arena>>, ()> {
        let (_lock_idx, lock) = work_item.next_lock(NetlistRef::Wire(obj));
        let lock_gotten = if !want_write {
            lock.ordered_try_read(self.stroad, work_item.prio)?
        } else {
            lock.ordered_try_write(self.stroad, work_item.prio)?
        };
        if !lock_gotten {
            return Err(());
        }
        Ok(ROGuard { x: obj })
    }
}

#[derive(Debug)]
pub struct OrderedAlgorithmRWView<'arena, 'q> {
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
    pub(super) queue:
        &'q ordered_commit_queue::OrderedCommitQueue<&'arena WorkItem<'arena, 'arena>>,
    pub(super) debug_id: Cell<usize>,
}
impl<'arena, 'q> NetlistView<'arena> for OrderedAlgorithmRWView<'arena, 'q> {
    type CellROGuardTy = ROGuard<'arena, NetlistCell<'arena>>;
    type WireROGuardTy = ROGuard<'arena, NetlistWire<'arena>>;
    type CellOwningGuardTy = RWGuard<'arena, NetlistCell<'arena>>;
    type WireOwningGuardTy = RWGuard<'arena, NetlistWire<'arena>>;
    type MaybeWorkItem = &'arena WorkItem<'arena, 'arena>;

    fn new_cell<'wrapper>(
        &'wrapper mut self,
        work_item: Self::MaybeWorkItem,
        cell_type: Uuid,
        num_connections: usize,
    ) -> Self::CellOwningGuardTy {
        let (new, gen) = self
            .heap_thread_shard
            .allocate::<LockedObj<NetlistCell<'arena>>>();
        unsafe {
            LockedObj::init_ordered(new.as_mut_ptr(), gen);
            let _ = NetlistCell::init(
                (*new.as_mut_ptr()).payload.get(),
                cell_type,
                self.debug_id.get(),
                num_connections,
            );
            self.debug_id.set(self.debug_id.get() + 1);
            let new_ref = ObjRef {
                ptr: new.assume_init_ref(),
                gen,
            };
            let (lock_idx, lock) = work_item.next_lock(NetlistRef::Cell(new_ref));
            lock.state.set(LockState::LockedForOrderedWrite);
            Self::CellOwningGuardTy {
                x: new_ref,
                lock_idx,
            }
        }
    }
    fn new_wire<'wrapper>(
        &'wrapper mut self,
        work_item: Self::MaybeWorkItem,
    ) -> Self::WireOwningGuardTy {
        let (new, gen) = self
            .heap_thread_shard
            .allocate::<LockedObj<NetlistWire<'arena>>>();
        unsafe {
            LockedObj::init_ordered(new.as_mut_ptr(), gen);
            let _ = NetlistWire::init((*new.as_mut_ptr()).payload.get(), self.debug_id.get());
            self.debug_id.set(self.debug_id.get() + 1);
            let new_ref = ObjRef {
                ptr: new.assume_init_ref(),
                gen,
            };
            let (lock_idx, lock) = work_item.next_lock(NetlistRef::Wire(new_ref));
            lock.state.set(LockState::LockedForOrderedWrite);
            Self::WireOwningGuardTy {
                x: new_ref,
                lock_idx,
            }
        }
    }

    fn delete_cell<'wrapper>(
        &'wrapper mut self,
        work_item: Self::MaybeWorkItem,
        guard: Self::CellOwningGuardTy,
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
        work_item: Self::MaybeWorkItem,
        guard: Self::WireOwningGuardTy,
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
        work_item: Self::MaybeWorkItem,
        obj: NetlistCellRef<'arena>,
    ) -> Option<Self::CellROGuardTy> {
        // xxx can this be done more efficiently?
        for lock_idx in 0..work_item.locks_used.get() {
            let lock_i = unsafe { &*work_item.locks[lock_idx].assume_init_ref().get() };
            if lock_i.p == obj.type_erase() {
                if lock_i.state.get() != LockState::LockedForOrderedRead
                    && lock_i.state.get() != LockState::LockedForOrderedWrite
                {
                    panic!("Tried to access a node in the wrong state")
                }
                return Some(ROGuard { x: obj });
            }
        }
        panic!("Tried to access a node that wasn't tagged in phase 1")
    }
    fn get_cell_write<'wrapper>(
        &'wrapper mut self,
        work_item: Self::MaybeWorkItem,
        obj: NetlistCellRef<'arena>,
    ) -> Option<Self::CellOwningGuardTy> {
        // xxx can this be done more efficiently?
        for lock_idx in 0..work_item.locks_used.get() {
            let lock_i = unsafe { &*work_item.locks[lock_idx].assume_init_ref().get() };
            if lock_i.p == obj.type_erase() {
                if lock_i.state.get() != LockState::LockedForOrderedWrite {
                    panic!("Tried to access a node in the wrong state")
                }
                return Some(RWGuard { x: obj, lock_idx });
            }
        }
        panic!("Tried to access a node that wasn't tagged in phase 1")
    }

    fn get_wire_read<'wrapper>(
        &'wrapper mut self,
        work_item: Self::MaybeWorkItem,
        obj: NetlistWireRef<'arena>,
    ) -> Option<Self::WireROGuardTy> {
        // xxx can this be done more efficiently?
        for lock_idx in 0..work_item.locks_used.get() {
            let lock_i = unsafe { &*work_item.locks[lock_idx].assume_init_ref().get() };
            if lock_i.p == obj.type_erase() {
                if lock_i.state.get() != LockState::LockedForOrderedRead
                    && lock_i.state.get() != LockState::LockedForOrderedWrite
                {
                    panic!("Tried to access a node in the wrong state")
                }
                return Some(ROGuard { x: obj });
            }
        }
        panic!("Tried to access a node that wasn't tagged in phase 1")
    }
    fn get_wire_write<'wrapper>(
        &'wrapper mut self,
        work_item: Self::MaybeWorkItem,
        obj: NetlistWireRef<'arena>,
    ) -> Option<Self::WireOwningGuardTy> {
        // xxx can this be done more efficiently?
        for lock_idx in 0..work_item.locks_used.get() {
            let lock_i = unsafe { &*work_item.locks[lock_idx].assume_init_ref().get() };
            if lock_i.p == obj.type_erase() {
                if lock_i.state.get() != LockState::LockedForOrderedWrite {
                    panic!("Tried to access a node in the wrong state")
                }
                return Some(RWGuard { x: obj, lock_idx });
            }
        }
        panic!("Tried to access a node that wasn't tagged in phase 1")
    }

    fn add_work<'wrapper>(&'wrapper mut self, node: NetlistRef<'arena>, mut prio: u64) {
        assert!(prio < i64::MAX as u64);

        // HAXXXX
        prio = 0;

        let (new, _gen) = self.heap_thread_shard.allocate::<WorkItem>();
        let work_item = unsafe { WorkItem::init(new.as_mut_ptr(), node) };
        work_item.prio = prio;
        self.queue.create_new_work(ItemWithPriority {
            item: work_item,
            prio: prio as i64,
        });
    }
}
