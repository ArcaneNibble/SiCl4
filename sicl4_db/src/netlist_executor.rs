//! Manages a netlist and running algorithms on it

use std::{
    alloc::Layout,
    cell::{Cell, UnsafeCell},
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    sync::atomic::Ordering,
    thread,
};

use crate::{allocator::*, locking::*, netlist::*, stroad::*};

pub trait UnorderedAlgorithm: Send + Sync {
    type ROtoRWTy;

    fn try_process_readonly<'algo_state, 'view, 'arena, 'work_item>(
        &'algo_state self,
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

const NUM_THREADS_FOR_NOW: usize = 1;
const MAX_ORDERED_LOCKS_PER_WORK_ITEM: usize = 4;

#[derive(Debug)]
struct WorkItemPayload<'arena, 'work_item> {
    w: &'work_item WorkItem<'arena, 'work_item>,
    guard_handed_out: Cell<bool>,
}
impl<'arena, 'work_item> StroadToWorkItemLink for WorkItemPayload<'arena, 'work_item> {
    fn cancel<'lock_inst, K>(e: &'lock_inst mut StroadNode<'lock_inst, K, Self>)
    where
        Self: Sized,
    {
        e.work_item_link.w.cancel()
    }

    fn unpark<'lock_inst, K>(e: &'lock_inst mut StroadNode<'lock_inst, K, Self>)
    where
        Self: Sized,
    {
        e.work_item_link.w.unpark()
    }
}

#[derive(Debug)]
pub struct WorkItem<'arena, 'work_item> {
    seed_node: NetlistRef<'arena>,
    locks_used: Cell<usize>,
    locks: [MaybeUninit<
        UnsafeCell<RWLock<'arena, 'work_item, WorkItemPayload<'arena, 'work_item>>>,
    >; MAX_ORDERED_LOCKS_PER_WORK_ITEM],
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
        &'work_item mut RWLock<'arena, 'work_item, WorkItemPayload<'arena, 'work_item>>,
    ) {
        let lock_idx = self.locks_used.get();
        if lock_idx == MAX_ORDERED_LOCKS_PER_WORK_ITEM {
            todo!("need to allocate a spill block?");
        }
        self.locks_used.set(lock_idx + 1);
        unsafe {
            let lock_ptr = (*self.locks[lock_idx].as_ptr()).get();
            RWLock::init(lock_ptr, obj.type_erase());
            let inner_payload = RWLock::unsafe_inner_payload_ptr(lock_ptr);
            // lifetimes should've made it s.t. this is pinned in place
            (*inner_payload).w = self;
            (*inner_payload).guard_handed_out = Cell::new(false);
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
    stroad: Box<Stroad<'arena, TypeErasedObjRef<'arena>, WorkItemPayload<'arena, 'arena>>>,
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
                        let seed_node = work_item.seed_node;
                        let ro_ret = algo.try_process_readonly(&mut ro_view, seed_node, work_item);
                        if ro_ret.is_err() {
                            println!("parked!");
                            continue;
                        }
                        let (ro_ret, work_item) = ro_ret.unwrap();

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

// the following code is for an *unordered* algorithm

#[derive(Debug)]
pub struct UnorderedAlgorithmROView<'arena> {
    stroad: &'arena Stroad<'arena, TypeErasedObjRef<'arena>, WorkItemPayload<'arena, 'arena>>,
    heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
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
    stroad: &'arena Stroad<'arena, TypeErasedObjRef<'arena>, WorkItemPayload<'arena, 'arena>>,
    heap_thread_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
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
                if lock_i.inner_payload_ref().guard_handed_out.get() {
                    panic!("Tried to access a node multiple times")
                    // xxx this is meh
                }
                lock_i.inner_payload_ref().guard_handed_out.set(true);
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
    lock: &'arena RWLock<'arena, 'arena, WorkItemPayload<'arena, 'arena>>,
    // todo fixme variance?
    _pd1: PhantomData<&'arena T>,
    // todo
    // pub x: ObjRef<'arena, T>,
}

// the following code is for *single-threaded* operation

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
        let _x: &dyn UnorderedAlgorithm<ROtoRWTy = u32>;
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
