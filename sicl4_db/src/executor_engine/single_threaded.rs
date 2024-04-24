//! This module contains code to support _inherently_ single-threaded operations
//! (i.e. operations that cannot be parallelized)

use super::*;

#[derive(Debug)]
pub struct SingleThreadedView<'arena> {
    pub(super) x: &'arena NetlistManager<'arena>,
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
    pub(super) debug_id: Cell<usize>,
}
// safety: only one of these objects can exist at once
unsafe impl<'arena> Send for SingleThreadedView<'arena> {}
impl<'arena> Drop for SingleThreadedView<'arena> {
    fn drop<'wrapper>(&'wrapper mut self) {
        self.x.in_use.set(false);
    }
}
impl<'arena> NetlistView<'arena> for SingleThreadedView<'arena> {
    type CellROGuardTy = SingleThreadedCellGuard<'arena>;
    type WireROGuardTy = SingleThreadedWireGuard<'arena>;
    type CellOwningGuardTy = SingleThreadedCellGuard<'arena>;
    type WireOwningGuardTy = SingleThreadedWireGuard<'arena>;
    type MaybeWorkItem = ();

    impl_view_shared_code!();

    fn get_cell_read<'wrapper>(
        &'wrapper mut self,
        _work_item: (),
        obj: NetlistCellRef<'arena>,
    ) -> Option<SingleThreadedCellGuard<'arena>> {
        let stored_lock_gen = obj.ptr.lock_and_generation.load(Ordering::Relaxed);
        if !lock_gen_valid(stored_lock_gen) || lock_gen_gen(stored_lock_gen) != obj.gen {
            return None;
        }
        if lock_gen_rwlock(stored_lock_gen) != 0 {
            // prevent multiple locks on the same node
            return None;
        }
        obj.ptr
            .lock_and_generation
            .fetch_or(0x7f, Ordering::Relaxed);
        Some(SingleThreadedObjGuard { x: obj })
    }
    fn get_cell_write<'wrapper>(
        &'wrapper mut self,
        _work_item: (),
        obj: NetlistCellRef<'arena>,
    ) -> Option<SingleThreadedCellGuard<'arena>> {
        self.get_cell_read(_work_item, obj)
    }

    fn get_wire_read<'wrapper>(
        &'wrapper mut self,
        _work_item: (),
        obj: NetlistWireRef<'arena>,
    ) -> Option<SingleThreadedWireGuard<'arena>> {
        let stored_lock_gen = obj.ptr.lock_and_generation.load(Ordering::Relaxed);
        if !lock_gen_valid(stored_lock_gen) || lock_gen_gen(stored_lock_gen) != obj.gen {
            return None;
        }
        if lock_gen_rwlock(stored_lock_gen) != 0 {
            // prevent multiple locks on the same node
            return None;
        }
        obj.ptr
            .lock_and_generation
            .fetch_or(0x7f, Ordering::Relaxed);
        Some(SingleThreadedObjGuard { x: obj })
    }
    fn get_wire_write<'wrapper>(
        &'wrapper mut self,
        _work_item: (),
        obj: NetlistWireRef<'arena>,
    ) -> Option<SingleThreadedWireGuard<'arena>> {
        self.get_wire_read(_work_item, obj)
    }
}
impl<'arena> SingleThreadedView<'arena> {
    // fixme is there any reason for these to expose &mut?

    pub fn new_work_item<'wrapper>(
        &'wrapper mut self,
        node: NetlistRef<'arena>,
    ) -> &'arena mut WorkItem<'arena, 'arena> {
        let (new, _gen) = self.heap_thread_shard.allocate::<WorkItem>();
        unsafe { WorkItem::init(new.as_mut_ptr(), node) }
    }

    pub fn delete_work_item<'wrapper>(
        &'wrapper mut self,
        work_item: &'arena mut WorkItem<'arena, 'arena>,
    ) {
        unsafe { self.heap_thread_shard.free(work_item) }
    }
}
type SingleThreadedCellGuard<'arena> = SingleThreadedObjGuard<'arena, NetlistCell<'arena>>;
type SingleThreadedWireGuard<'arena> = SingleThreadedObjGuard<'arena, NetlistWire<'arena>>;
#[derive(Debug)]
pub struct SingleThreadedObjGuard<'arena, T> {
    pub x: ObjRef<'arena, T>,
}
impl<'arena, T> SingleThreadedObjGuard<'arena, T> {
    pub fn ref_<'guard>(&'guard self) -> ObjRef<'arena, T> {
        self.x
    }
}
impl<'arena, T> NetlistGuard<'arena, T> for SingleThreadedObjGuard<'arena, T> {
    fn ref_<'guard>(&'guard self) -> ObjRef<'arena, T> {
        self.x
    }
}
impl<'arena, T> Drop for SingleThreadedObjGuard<'arena, T> {
    fn drop(&mut self) {
        self.x
            .ptr
            .lock_and_generation
            .fetch_and(!0x7f, Ordering::Relaxed);
    }
}
impl<'arena, T> Deref for SingleThreadedObjGuard<'arena, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // safety: single-threaded environment
        unsafe { &*self.x.ptr.payload.get() }
    }
}
impl<'arena, T> DerefMut for SingleThreadedObjGuard<'arena, T> {
    fn deref_mut(&mut self) -> &mut T {
        // safety: single-threaded environment
        unsafe { &mut *self.x.ptr.payload.get() }
    }
}
