//! Manages a netlist and running algorithms on it

use std::{
    alloc::Layout,
    cell::Cell,
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    sync::atomic::Ordering,
    thread,
};

use crate::{allocator::*, locking::*, netlist::*, stroad::*};

pub trait UnorderedAlgorithm: Send + Sync {
    fn process_node<'algo_state, 'view, 'arena, 'work_item>(
        &'algo_state self,
        view: &'view mut UnorderedAlgorithmThreadView,
        node: NetlistRef<'arena>,
        work_item: &'work_item mut WorkItem<'arena, 'work_item>,
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
        e.payload.w.cancel()
    }

    fn unpark<'lock_inst, K>(e: &'lock_inst mut LockInstance<'lock_inst, K, Self>)
    where
        Self: Sized,
    {
        e.payload.w.unpark()
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

    fn unpark(&'work_item self) {
        todo!()
    }

    fn cancel(&'work_item self) {
        todo!()
    }
}

/// Top-level netlist + work items unified data structure
///
/// This doesn't actually *have* to be unified, but it's simpler this way
#[derive(Debug)]
pub struct NetlistManager<'arena> {
    heap: SlabRoot<'arena, NetlistTypeMapper>,
    stroad: Box<Stroad<'arena, NetlistRef<'arena>, WorkItemPayload<'arena, 'arena>>>,
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
                    let mut view = UnorderedAlgorithmThreadView {
                        stroad,
                        heap_thread_shard,
                    };
                    while let Some(work_item) = local_queue.pop() {
                        let _ret = algo.process_node(&mut view, work_item.seed_node, work_item);
                    }
                });
            }
        });
        self.in_use.set(false);
    }
}

#[derive(Debug)]
pub struct UnorderedAlgorithmThreadView<'arena> {
    stroad: &'arena Stroad<'arena, NetlistRef<'arena>, WorkItemPayload<'arena, 'arena>>,
    heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
}
impl<'arena> UnorderedAlgorithmThreadView<'arena> {}

#[derive(Debug)]
pub struct SingleThreadedView<'arena> {
    x: &'arena NetlistManager<'arena>,
    heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn executor_ensure_obj_safety() {
        let _x: &dyn UnorderedAlgorithm;
    }

    #[cfg(not(loom))]
    #[test]
    #[should_panic]
    fn executor_single_threaded_only_one() {
        let manager = NetlistManager::new();
        let _view1 = manager.access_single_threaded();
        let _view2 = manager.access_single_threaded();
    }

    #[cfg(not(loom))]
    #[test]
    fn executor_single_threaded_smoke_test() {
        let manager = NetlistManager::new();
        let mut view = manager.access_single_threaded();
        let cell_ref;
        let wire_ref;
        {
            let mut cell = view.new_cell();
            dbg!(&cell);
            dbg!(&*cell);
            cell_ref = cell.x;
            let mut wire = view.new_wire();
            dbg!(&wire);
            dbg!(&*wire);
            wire_ref = wire.x;
            let work_item = view.new_work_item(cell_ref.into());
            dbg!(work_item);

            cell._wire = Some(wire_ref);
            wire._cell = Some(cell_ref);
        }
        {
            let cell_again = view.get_cell(cell_ref).unwrap();
            let wire_again = view.get_wire(wire_ref).unwrap();
            assert_eq!(cell_again._wire, Some(wire_ref));
            assert_eq!(wire_again._cell, Some(cell_ref));
            view.delete_cell(cell_again);
            view.delete_wire(wire_again);
        }
        {
            let cell_again_again = view.get_cell(cell_ref);
            let wire_again_again = view.get_wire(wire_ref);
            assert!(cell_again_again.is_none());
            assert!(wire_again_again.is_none());
        }
    }

    #[cfg(not(loom))]
    #[test]
    fn executor_single_threaded_only_one_get() {
        let manager = NetlistManager::new();
        let mut view = manager.access_single_threaded();
        let cell = view.new_cell();
        let cell_ref = cell.x;
        drop(cell);

        let cell_again_0 = view.get_cell(cell_ref);
        let cell_again_1 = view.get_cell(cell_ref);
        assert!(cell_again_0.is_some());
        assert!(cell_again_1.is_none());
    }

    #[cfg(not(loom))]
    #[test]
    fn executor_asdf() {
        let manager = NetlistManager::new();
        let mut view = manager.access_single_threaded();
        let cell = view.new_cell();
        dbg!(&cell);
        dbg!(&*cell);
        let wire = view.new_wire();
        dbg!(&wire);
        dbg!(&*wire);
        let work_item = view.new_work_item(cell.x.into());
        dbg!(work_item);
        drop(view);
        let cell_ref = cell.x;
        drop(cell);

        let mut view = manager.access_single_threaded();
        let cell2 = view.get_cell(cell_ref);
        dbg!(&cell2);
        let cell3 = view.get_cell(cell_ref);
        dbg!(&cell3);
    }
}
