//! This module contains code to support operations where the order does not matter.
//!
//! In other words, the "fringe" of the graph algorithm is an unordered set.

use super::*;

pub trait UnorderedAlgorithm: Send + Sync {
    type ROtoRWTy;

    fn try_process_readonly<'algo_global_state, 'view, 'arena>(
        &'algo_global_state self,
        view: &'view mut UnorderedAlgorithmROView<'arena>,
        work_item: &'arena WorkItem<'arena, 'arena>,
    ) -> Result<Self::ROtoRWTy, ()>;

    fn process_finish_readwrite<'algo_state, 'view, 'arena>(
        &'algo_state self,
        view: &'view mut UnorderedAlgorithmRWView<'arena>,
        work_item: &'arena WorkItem<'arena, 'arena>,
        ro_output: Self::ROtoRWTy,
    );
}

#[derive(Debug)]
pub struct UnorderedAlgorithmROView<'arena> {
    pub(super) stroad:
        &'arena Stroad<'arena, TypeErasedObjRef<'arena>, WorkItemPerLockData<'arena, 'arena>>,
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
}
impl<'arena> UnorderedAlgorithmROView<'arena> {
    pub fn try_lock_cell<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
        want_write: bool,
    ) -> Result<UnorderedObjPhase1Guard<'arena, NetlistCell<'arena>>, ()> {
        let (_lock_idx, lock) = work_item.next_lock(NetlistRef::Cell(obj));
        let lock_gotten = if !want_write {
            lock.unordered_try_read(self.stroad)?
        } else {
            lock.unordered_try_write(self.stroad)?
        };
        if !lock_gotten {
            return Err(());
        }
        Ok(UnorderedObjPhase1Guard { x: obj })
    }

    pub fn try_lock_wire<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistWireRef<'arena>,
        want_write: bool,
    ) -> Result<UnorderedObjPhase1Guard<'arena, NetlistWire<'arena>>, ()> {
        let (_lock_idx, lock) = work_item.next_lock(NetlistRef::Wire(obj));
        let lock_gotten = if !want_write {
            lock.unordered_try_read(self.stroad)?
        } else {
            lock.unordered_try_write(self.stroad)?
        };
        if !lock_gotten {
            return Err(());
        }
        Ok(UnorderedObjPhase1Guard { x: obj })
    }
}

#[derive(Debug)]
pub struct UnorderedAlgorithmRWView<'arena> {
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
}
impl<'arena> UnorderedAlgorithmRWView<'arena> {
    pub fn get_cell_read<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
    ) -> UnorderedObjPhase2ROGuard<'arena, NetlistCell<'arena>> {
        // xxx can this be done more efficiently?
        for lock_idx in 0..work_item.locks_used.get() {
            let lock_i = unsafe { &*work_item.locks[lock_idx].assume_init_ref().get() };
            if lock_i.p == obj.type_erase() {
                if lock_i.state.get() != LockState::LockedForUnorderedRead
                    && lock_i.state.get() != LockState::LockedForUnorderedWrite
                {
                    panic!("Tried to access a node in the wrong state")
                }
                if lock_i
                    .stroad_work_item_link()
                    .guard_handed_out
                    .load(Ordering::Relaxed)
                {
                    panic!("Tried to access a node multiple times")
                    // xxx this is meh
                }
                lock_i
                    .stroad_work_item_link()
                    .guard_handed_out
                    .store(true, Ordering::Relaxed);
                return UnorderedObjPhase2ROGuard { x: obj };
            }
        }
        panic!("Tried to access a node that wasn't tagged in phase 1")
    }

    pub fn get_cell_write<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
    ) -> UnorderedObjPhase2RWGuard<'arena, NetlistCell<'arena>> {
        // xxx can this be done more efficiently?
        for lock_idx in 0..work_item.locks_used.get() {
            let lock_i = unsafe { &*work_item.locks[lock_idx].assume_init_ref().get() };
            if lock_i.p == obj.type_erase() {
                if lock_i.state.get() != LockState::LockedForUnorderedWrite {
                    panic!("Tried to access a node in the wrong state")
                }
                if lock_i
                    .stroad_work_item_link()
                    .guard_handed_out
                    .load(Ordering::Relaxed)
                {
                    panic!("Tried to access a node multiple times")
                    // xxx this is meh
                }
                lock_i
                    .stroad_work_item_link()
                    .guard_handed_out
                    .store(true, Ordering::Relaxed);
                return UnorderedObjPhase2RWGuard { x: obj };
            }
        }
        panic!("Tried to access a node that wasn't tagged in phase 1")
    }

    pub fn get_wire_read<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistWireRef<'arena>,
    ) -> UnorderedObjPhase2ROGuard<'arena, NetlistWire<'arena>> {
        // xxx can this be done more efficiently?
        for lock_idx in 0..work_item.locks_used.get() {
            let lock_i = unsafe { &*work_item.locks[lock_idx].assume_init_ref().get() };
            if lock_i.p == obj.type_erase() {
                if lock_i.state.get() != LockState::LockedForUnorderedRead
                    && lock_i.state.get() != LockState::LockedForUnorderedWrite
                {
                    panic!("Tried to access a node in the wrong state")
                }
                if lock_i
                    .stroad_work_item_link()
                    .guard_handed_out
                    .load(Ordering::Relaxed)
                {
                    panic!("Tried to access a node multiple times")
                    // xxx this is meh
                }
                lock_i
                    .stroad_work_item_link()
                    .guard_handed_out
                    .store(true, Ordering::Relaxed);
                return UnorderedObjPhase2ROGuard { x: obj };
            }
        }
        panic!("Tried to access a node that wasn't tagged in phase 1")
    }

    pub fn get_wire_write<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistWireRef<'arena>,
    ) -> UnorderedObjPhase2RWGuard<'arena, NetlistWire<'arena>> {
        // xxx can this be done more efficiently?
        for lock_idx in 0..work_item.locks_used.get() {
            let lock_i = unsafe { &*work_item.locks[lock_idx].assume_init_ref().get() };
            if lock_i.p == obj.type_erase() {
                if lock_i.state.get() != LockState::LockedForUnorderedWrite {
                    panic!("Tried to access a node in the wrong state")
                }
                if lock_i
                    .stroad_work_item_link()
                    .guard_handed_out
                    .load(Ordering::Relaxed)
                {
                    panic!("Tried to access a node multiple times")
                    // xxx this is meh
                }
                lock_i
                    .stroad_work_item_link()
                    .guard_handed_out
                    .store(true, Ordering::Relaxed);
                return UnorderedObjPhase2RWGuard { x: obj };
            }
        }
        panic!("Tried to access a node that wasn't tagged in phase 1")
    }
}

#[derive(Debug)]
pub struct UnorderedObjPhase1Guard<'arena, T> {
    pub x: ObjRef<'arena, T>,
}
impl<'arena, T> Deref for UnorderedObjPhase1Guard<'arena, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // safety: atomic ops (in lock_ops) ensures that there is no conflict
        unsafe { &*self.x.ptr.payload.get() }
    }
}

#[derive(Debug)]
pub struct UnorderedObjPhase2ROGuard<'arena, T> {
    pub x: ObjRef<'arena, T>,
}
impl<'arena, T> Deref for UnorderedObjPhase2ROGuard<'arena, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // safety: atomic ops (in lock_ops) ensures that there is no conflict
        unsafe { &*self.x.ptr.payload.get() }
    }
}

#[derive(Debug)]
pub struct UnorderedObjPhase2RWGuard<'arena, T> {
    pub x: ObjRef<'arena, T>,
}
impl<'arena, T> Deref for UnorderedObjPhase2RWGuard<'arena, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // safety: atomic ops (in lock_ops) ensures that there is no conflict
        unsafe { &*self.x.ptr.payload.get() }
    }
}
impl<'arena, T> DerefMut for UnorderedObjPhase2RWGuard<'arena, T> {
    fn deref_mut(&mut self) -> &mut T {
        // safety: atomic ops (in lock_ops) ensures that there is no conflict
        unsafe { &mut *self.x.ptr.payload.get() }
    }
}
