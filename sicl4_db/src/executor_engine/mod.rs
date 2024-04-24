//! Manages a netlist and running algorithms on it

use std::{
    alloc::Layout,
    cell::{Cell, RefCell, UnsafeCell},
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    rc::Rc,
    sync::atomic::Ordering,
    thread,
};

use crate::allocator::*;
use crate::lock_ops::*;
use crate::loom_testing::*;
use crate::netlist::*;
use crate::stroad::*;

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
    pub fn cell(self) -> NetlistCellRef<'arena> {
        match self {
            NetlistRef::Cell(x) => x,
            _ => panic!("Not a Cell"),
        }
    }
    pub fn wire(self) -> NetlistWireRef<'arena> {
        match self {
            NetlistRef::Wire(x) => x,
            _ => panic!("Not a Wire"),
        }
    }

    fn type_erase(self) -> TypeErasedObjRef<'arena> {
        match self {
            NetlistRef::Cell(x) => x.type_erase(),
            NetlistRef::Wire(x) => x.type_erase(),
        }
    }
}

/// guards must allow for extracting the target ptr
pub trait NetlistGuard<'arena, T> {
    fn ref_<'guard>(&'guard self) -> ObjRef<'arena, T>;
}

/// common API for doing stuff to a netlist
pub trait NetlistView<'arena> {
    type CellROGuardTy: NetlistGuard<'arena, NetlistCell<'arena>>
        + Deref<Target = NetlistCell<'arena>>;
    type WireROGuardTy: NetlistGuard<'arena, NetlistWire<'arena>>
        + Deref<Target = NetlistWire<'arena>>;
    type CellOwningGuardTy: NetlistGuard<'arena, NetlistCell<'arena>>
        + DerefMut<Target = NetlistCell<'arena>>;
    type WireOwningGuardTy: NetlistGuard<'arena, NetlistWire<'arena>>
        + DerefMut<Target = NetlistWire<'arena>>;
    type MaybeWorkItem;

    fn new_cell<'wrapper>(
        &'wrapper mut self,
        cell_type: Uuid,
        num_connections: usize,
    ) -> Self::CellOwningGuardTy;
    fn new_wire<'wrapper>(&'wrapper mut self) -> Self::WireOwningGuardTy;
    fn delete_cell<'wrapper>(&'wrapper mut self, guard: Self::CellOwningGuardTy);
    fn delete_wire<'wrapper>(&'wrapper mut self, guard: Self::WireOwningGuardTy);

    // fixme document the semantics of Option
    fn get_cell_read<'wrapper>(
        &'wrapper mut self,
        work_item: Self::MaybeWorkItem,
        obj: NetlistCellRef<'arena>,
    ) -> Option<Self::CellROGuardTy>;
    fn get_cell_write<'wrapper>(
        &'wrapper mut self,
        work_item: Self::MaybeWorkItem,
        obj: NetlistCellRef<'arena>,
    ) -> Option<Self::CellOwningGuardTy>;

    fn get_wire_read<'wrapper>(
        &'wrapper mut self,
        work_item: Self::MaybeWorkItem,
        obj: NetlistWireRef<'arena>,
    ) -> Option<Self::WireROGuardTy>;
    fn get_wire_write<'wrapper>(
        &'wrapper mut self,
        work_item: Self::MaybeWorkItem,
        obj: NetlistWireRef<'arena>,
    ) -> Option<Self::WireOwningGuardTy>;

    fn add_work<'wrapper>(&'wrapper mut self, node: NetlistRef<'arena>);
}
macro_rules! impl_view_shared_code {
    () => {
        fn new_cell<'wrapper>(
            &'wrapper mut self,
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
                Self::CellOwningGuardTy { x: new_ref }
            }
        }
        fn new_wire<'wrapper>(&'wrapper mut self) -> Self::WireOwningGuardTy {
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
                Self::WireOwningGuardTy { x: new_ref }
            }
        }

        fn delete_cell<'wrapper>(&'wrapper mut self, guard: Self::CellOwningGuardTy) {
            guard.x.ptr.lock_and_generation.store(0, Ordering::Relaxed);
            unsafe {
                // safety: the guard represents exclusive access to the node
                self.heap_thread_shard.free(guard.x.ptr)
            }
            mem::forget(guard);
        }
        fn delete_wire<'wrapper>(&'wrapper mut self, guard: Self::WireOwningGuardTy) {
            guard.x.ptr.lock_and_generation.store(0, Ordering::Relaxed);
            unsafe {
                // safety: the guard represents exclusive access to the node
                self.heap_thread_shard.free(guard.x.ptr)
            }
            mem::forget(guard);
        }
    };
}

const MAX_LOCKS_PER_WORK_ITEM: usize = 4;

#[derive(Debug)]
struct WorkItemPerLockData<'arena, 'work_item> {
    w: &'work_item WorkItem<'arena, 'work_item>,
}
impl<'arena, 'work_item> StroadToWorkItemLink for WorkItemPerLockData<'arena, 'work_item> {
    fn cancel(&self) {
        self.w.cancel()
    }

    fn unpark(&self, q: &mut Self::UnparkXtraTy) {
        self.w.unpark(q)
    }

    type UnparkXtraTy = LocalQueue<&'work_item WorkItem<'arena, 'work_item>>;
}

#[derive(Debug)]
pub struct WorkItem<'arena, 'work_item> {
    pub seed_node: NetlistRef<'arena>,
    _todo_wip_did_unpark: AtomicBool,
    _todo_wip_cancelled: AtomicBool,
    locks_used: Cell<usize>,
    locks: [MaybeUninit<
        UnsafeCell<LockAndStroadData<'arena, 'work_item, WorkItemPerLockData<'arena, 'work_item>>>,
    >; MAX_LOCKS_PER_WORK_ITEM],
}
// xxx fixme wtf is this
// xxx fixme the entire safety of this needs to be figured out, since it has unsafe inner mutability
unsafe impl<'arena, 'work_item> Send for WorkItem<'arena, 'work_item> {}
unsafe impl<'arena, 'work_item> Sync for WorkItem<'arena, 'work_item> {}
impl<'arena, 'work_item> WorkItem<'arena, 'work_item> {
    pub unsafe fn init(self_: *mut Self, node: NetlistRef<'arena>) -> &'work_item mut Self {
        (*self_).seed_node = node;
        (*self_)._todo_wip_did_unpark = AtomicBool::new(false);
        (*self_)._todo_wip_cancelled = AtomicBool::new(false);
        (*self_).locks_used = Cell::new(0);
        &mut *self_
    }

    fn unpark(
        &'work_item self,
        local_queue: &mut LocalQueue<&'work_item WorkItem<'arena, 'work_item>>,
    ) {
        // unpark happens *only* on lock release
        // and *only* happens once
        // it happens for both ordered and unordered algorithms
        // it cannot happen multiple times simultaneously from different threads, because
        // a work item can only be blocked on *one* lock at a time (at least in a correct impl).
        // additionally, unparking happens with the stroad bucket lock held -- can only happen from one thread

        // we *do* need to actually check the "only unpark once" requirement though
        if !self._todo_wip_did_unpark.swap(true, Ordering::Relaxed) {
            local_queue.push(self);
        }
    }

    fn cancel(&'work_item self) {
        // cancel happens *only* on lock acquisition
        // it happens *only* for ordered algorithms
        // it can happen multiple times in a multithreaded race-prone way, because
        // even though cancelling happens with the stroad bucket lock held,
        // a speculative work item waiting to commit can hold multiple *different* locks.
        // a cancellation can be triggered because of two *different* ones in a racy way
        self._todo_wip_cancelled.store(true, Ordering::Relaxed);
    }

    fn next_lock(
        &'work_item self,
        obj: NetlistRef<'arena>,
    ) -> (
        usize,
        &'work_item mut LockAndStroadData<
            'arena,
            'work_item,
            WorkItemPerLockData<'arena, 'work_item>,
        >,
    ) {
        let lock_idx = self.locks_used.get();
        if lock_idx == MAX_LOCKS_PER_WORK_ITEM {
            todo!("need to allocate a spill block?");
        }
        self.locks_used.set(lock_idx + 1);
        unsafe {
            let lock_ptr = (*self.locks[lock_idx].as_ptr()).get();
            LockAndStroadData::init(lock_ptr, obj.type_erase());
            let inner_payload = LockAndStroadData::unsafe_stroad_work_item_link_ptr(lock_ptr);
            // lifetimes should've made it s.t. this is pinned in place
            (*inner_payload).w = self;
            (lock_idx, &mut *lock_ptr)
        }
    }

    /// after this work item pops back out after unparking, reset everything so that it's ready to try again
    fn reset_state(&self) {
        self._todo_wip_did_unpark.store(false, Ordering::Relaxed);
        self._todo_wip_cancelled.store(false, Ordering::Relaxed);
        self.locks_used.set(0);
    }
}

/// Top-level netlist + work items unified data structure
///
/// This doesn't actually *have* to be unified, but it's simpler this way
#[derive(Debug)]
pub struct NetlistManager<'arena> {
    heap: SlabRoot<'arena, NetlistTypeMapper>,
    stroad: Box<Stroad<'arena, TypeErasedObjRef<'arena>, WorkItemPerLockData<'arena, 'arena>>>,
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

    pub fn access_single_threaded<'q>(
        &'arena self,
        queue: &'q work_queue::Queue<&'arena WorkItem<'arena, 'arena>>,
    ) -> SingleThreadedView<'arena, 'q> {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        SingleThreadedView {
            x: self,
            heap_thread_shard: self.heap.new_thread(),
            workqueue: queue,
            debug_id: Cell::new(0),
        }
    }

    pub fn run_unordered_algorithm<A: UnorderedAlgorithm>(
        &'arena self,
        algo: &A,
        queue: &work_queue::Queue<&'arena WorkItem<'arena, 'arena>>,
    ) {
        assert!(!self.in_use.get());
        self.in_use.set(true);
        thread::scope(|s| {
            for local_queue in queue.local_queues() {
                let heap_thread_shard = self.heap.new_thread();
                let stroad = &self.stroad;
                s.spawn(move || {
                    let local_queue_rc = Rc::new(RefCell::new(local_queue));
                    let mut ro_view = UnorderedAlgorithmROView {
                        stroad,
                        heap_thread_shard,
                    };
                    while let Some(work_item) = {
                        let mut q = local_queue_rc.borrow_mut();
                        let work_item = q.pop();
                        drop(q);
                        work_item
                    } {
                        work_item.reset_state();
                        let ro_ret = algo.try_process_readonly(&mut ro_view, work_item);
                        if ro_ret.is_err() {
                            println!("parked!");
                            unsafe {
                                let locks_used = work_item.locks_used.get();
                                let lock_that_failed =
                                    &*work_item.locks[locks_used - 1].assume_init_ref().get();
                                debug_assert!(lock_that_failed.state.get() == LockState::Parked);

                                // release all the other locks, as we failed to speculative grab what we needed
                                for lock_idx in 0..(locks_used - 1) {
                                    let lock = &*work_item.locks[lock_idx].assume_init_ref().get();
                                    debug_assert!(
                                        (lock.state.get() == LockState::LockedForUnorderedRead)
                                            || lock.state.get()
                                                == LockState::LockedForUnorderedWrite
                                    );
                                    lock.unlock(stroad, &mut local_queue_rc.borrow_mut());
                                }
                            }
                            continue;
                        }
                        let ro_ret = ro_ret.unwrap();

                        let heap_thread_shard = {
                            let mut rw_view = UnorderedAlgorithmRWView {
                                heap_thread_shard: ro_view.heap_thread_shard,
                                queue: &mut local_queue_rc.borrow_mut(),
                                debug_id: Cell::new(0), // XXX totally fuckered
                            };
                            algo.process_finish_readwrite(&mut rw_view, work_item, ro_ret);
                            rw_view.heap_thread_shard
                        };
                        unsafe {
                            // release *all* locks, even if the RW phase didn't use one
                            let locks_used = work_item.locks_used.get();
                            for lock_idx in 0..locks_used {
                                let lock = &*work_item.locks[lock_idx].assume_init_ref().get();
                                debug_assert!(
                                    (lock.state.get() == LockState::LockedForUnorderedRead)
                                        || lock.state.get() == LockState::LockedForUnorderedWrite
                                );
                                lock.unlock(stroad, &mut local_queue_rc.borrow_mut());
                            }
                        }
                        ro_view = UnorderedAlgorithmROView {
                            stroad,
                            heap_thread_shard,
                        };
                    }
                });
            }
        });
        self.in_use.set(false);
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

mod single_threaded;
pub use single_threaded::*;

mod unordered;
pub use unordered::*;
use uuid::Uuid;
use work_queue::LocalQueue;

#[cfg(test)]
mod tests;
