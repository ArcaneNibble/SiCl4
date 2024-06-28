//! This module contains code to support _inherently_ single-threaded operations
//! (i.e. operations that cannot be parallelized)

use super::*;

#[derive(Debug)]
pub struct SingleThreadedView<'arena, 'q> {
    pub(super) x: &'arena NetlistManager<'arena>,
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
    pub(super) workqueue: &'q work_queue::Queue<&'arena WorkItem<'arena, 'arena>>,
    pub(super) debug_id: Cell<usize>,
}
// safety: only one of these objects can exist at once
unsafe impl<'arena, 'q> Send for SingleThreadedView<'arena, 'q> {}
impl<'arena, 'q> Drop for SingleThreadedView<'arena, 'q> {
    fn drop<'wrapper>(&'wrapper mut self) {
        self.x.in_use.set(false);
    }
}
impl<'arena, 'q> NetlistView<'arena> for SingleThreadedView<'arena, 'q> {
    type CellROGuardTy = SingleThreadedCellGuard<'arena>;
    type WireROGuardTy = SingleThreadedWireGuard<'arena>;
    type CellOwningGuardTy = SingleThreadedCellGuard<'arena>;
    type WireOwningGuardTy = SingleThreadedWireGuard<'arena>;
    type MaybeWorkItem = ();

    fn new_cell<'wrapper>(
        &'wrapper mut self,
        _work_item: (),
        cell_type: Uuid,
        num_connections: usize,
    ) -> Self::CellOwningGuardTy {
        let (new, gen) = self
            .heap_thread_shard
            .allocate::<LockedObj<NetlistCell<'arena>>>();
        unsafe {
            LockedObj::init(new.as_mut_ptr(), gen, 0x7f);
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
            SingleThreadedObjGuard { x: new_ref }
        }
    }
    fn new_wire<'wrapper>(&'wrapper mut self, _work_item: ()) -> Self::WireOwningGuardTy {
        let (new, gen) = self
            .heap_thread_shard
            .allocate::<LockedObj<NetlistWire<'arena>>>();
        unsafe {
            LockedObj::init(new.as_mut_ptr(), gen, 0x7f);
            let _ = NetlistWire::init((*new.as_mut_ptr()).payload.get(), self.debug_id.get());
            self.debug_id.set(self.debug_id.get() + 1);
            let new_ref = ObjRef {
                ptr: new.assume_init_ref(),
                gen,
            };
            SingleThreadedObjGuard { x: new_ref }
        }
    }

    fn delete_cell<'wrapper>(&'wrapper mut self, _work_item: (), guard: Self::CellOwningGuardTy) {
        guard.x.ptr.lock_and_generation.store(0, Ordering::Relaxed);
        unsafe {
            // safety: the guard represents exclusive access to the node
            self.heap_thread_shard.free(guard.x.ptr)
        }
        mem::forget(guard);
    }
    fn delete_wire<'wrapper>(&'wrapper mut self, _work_item: (), guard: Self::WireOwningGuardTy) {
        guard.x.ptr.lock_and_generation.store(0, Ordering::Relaxed);
        unsafe {
            // safety: the guard represents exclusive access to the node
            self.heap_thread_shard.free(guard.x.ptr)
        }
        mem::forget(guard);
    }

    fn get_cell_read<'wrapper>(
        &'wrapper mut self,
        _work_item: (),
        obj: NetlistCellRef<'arena>,
    ) -> Option<Self::CellROGuardTy> {
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
    ) -> Option<Self::CellOwningGuardTy> {
        self.get_cell_read(_work_item, obj)
    }

    fn get_wire_read<'wrapper>(
        &'wrapper mut self,
        _work_item: (),
        obj: NetlistWireRef<'arena>,
    ) -> Option<Self::WireROGuardTy> {
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
    ) -> Option<Self::WireOwningGuardTy> {
        self.get_wire_read(_work_item, obj)
    }

    fn add_work<'wrapper>(&'wrapper mut self, node: NetlistRef<'arena>, _prio: u64) {
        let (new, _gen) = self.heap_thread_shard.allocate::<WorkItem>();
        let work_item = unsafe { WorkItem::init(new.as_mut_ptr(), node) };
        self.workqueue.push(&*work_item);
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
