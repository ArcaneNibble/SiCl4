//! This module contains code to support _inherently_ single-threaded operations
//! (i.e. operations that cannot be parallelized)

use super::*;

#[derive(Debug)]
pub struct SingleThreadedView<'arena> {
    pub(super) x: &'arena NetlistManager<'arena>,
    pub(super) heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
}
// safety: only one of these objects can exist at once
unsafe impl<'arena> Send for SingleThreadedView<'arena> {}
impl<'arena> Drop for SingleThreadedView<'arena> {
    fn drop<'wrapper>(&'wrapper mut self) {
        self.x.in_use.set(false);
    }
}
impl<'arena> SingleThreadedView<'arena> {
    pub fn new_cell<'wrapper>(&'wrapper mut self) -> SingleThreadedCellGuard<'arena> {
        let (new, gen) = self
            .heap_thread_shard
            .allocate::<LockedObj<NetlistCell<'arena>>>();
        unsafe {
            LockedObj::init(new.as_mut_ptr(), gen, 0x7f);
            let _ = NetlistCell::init((*new.as_mut_ptr()).payload.get());
            let new_ref = ObjRef {
                ptr: new.assume_init_ref(),
                gen,
            };
            SingleThreadedObjGuard { x: new_ref }
        }
    }

    pub fn new_wire<'wrapper>(&'wrapper mut self) -> SingleThreadedWireGuard<'arena> {
        let (new, gen) = self
            .heap_thread_shard
            .allocate::<LockedObj<NetlistWire<'arena>>>();
        unsafe {
            LockedObj::init(new.as_mut_ptr(), gen, 0x7f);
            let _ = NetlistWire::init((*new.as_mut_ptr()).payload.get());
            let new_ref = ObjRef {
                ptr: new.assume_init_ref(),
                gen,
            };
            SingleThreadedObjGuard { x: new_ref }
        }
    }

    pub fn get_cell<'wrapper>(
        &'wrapper mut self,
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

    pub fn get_wire<'wrapper>(
        &'wrapper mut self,
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

    pub fn delete_cell<'wrapper>(&'wrapper mut self, guard: SingleThreadedCellGuard<'arena>) {
        guard.x.ptr.lock_and_generation.store(0, Ordering::Relaxed);
        unsafe {
            // safety: the guard represents exclusive access to the node
            self.heap_thread_shard.free(guard.x.ptr)
        }
        mem::forget(guard);
    }

    pub fn delete_wire<'wrapper>(&'wrapper mut self, guard: SingleThreadedWireGuard<'arena>) {
        guard.x.ptr.lock_and_generation.store(0, Ordering::Relaxed);
        unsafe {
            // safety: the guard represents exclusive access to the node
            self.heap_thread_shard.free(guard.x.ptr)
        }
        mem::forget(guard);
    }

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
