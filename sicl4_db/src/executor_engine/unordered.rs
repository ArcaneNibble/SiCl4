//! This module contains code to support operations where the order does not matter.
//!
//! In other words, the "fringe" of the graph algorithm is an unordered set.

use super::*;

pub trait UnorderedAlgorithm: Send + Sync {
    type ROtoRWTy;

    fn try_process_readonly<'algo_global_state, 'view, 'arena, 'work_item>(
        &'algo_global_state self,
        view: &'view mut UnorderedAlgorithmROView,
        node: NetlistRef<'arena>,
        work_item: &'work_item mut WorkItem<'arena, 'work_item>,
    ) -> Result<(Self::ROtoRWTy, &'work_item mut WorkItem<'arena, 'work_item>), ()>;

    fn process_finish_readwrite<'algo_state, 'view, 'arena, 'work_item>(
        &'algo_state self,
        view: &'view mut UnorderedAlgorithmRWView,
        node: NetlistRef<'arena>,
        work_item: &'work_item mut WorkItem<'arena, 'work_item>,
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
    ) -> Result<UnorderedObjROGuard<'arena, NetlistCell<'arena>>, ()> {
        let (_lock_idx, lock) = work_item.next_lock(NetlistRef::Cell(obj));
        let lock_gotten = if !want_write {
            lock.unordered_try_read(self.stroad)?
        } else {
            lock.unordered_try_write(self.stroad)?
        };
        if !lock_gotten {
            return Err(());
        }
        Ok(UnorderedObjROGuard {
            lock,
            _pd1: PhantomData,
        })
    }
}

#[derive(Debug)]
pub struct UnorderedAlgorithmRWView<'arena> {
    pub(super) stroad:
        &'arena Stroad<'arena, TypeErasedObjRef<'arena>, WorkItemPerLockData<'arena, 'arena>>,
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
}
impl<'arena> UnorderedAlgorithmRWView<'arena> {
    pub fn get_cell_read<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena WorkItem<'arena, 'arena>,
        obj: NetlistCellRef<'arena>,
    ) -> UnorderedObjROGuard<'arena, NetlistCell<'arena>> {
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
                return UnorderedObjROGuard {
                    lock: lock_i,
                    _pd1: PhantomData,
                };
            }
        }
        panic!("Tried to access a node that wasn't tagged in RO phase")
    }
}

#[derive(Debug)]
pub struct UnorderedObjROGuard<'arena, T> {
    lock: &'arena LockAndStroadData<'arena, 'arena, WorkItemPerLockData<'arena, 'arena>>,
    // todo fixme variance?
    _pd1: PhantomData<&'arena T>,
    // todo
    // pub x: ObjRef<'arena, T>,
}
