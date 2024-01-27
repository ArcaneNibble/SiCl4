//! Core of the custom netlist data structure
//!
//! This contains logic for managing locks on netlist nodes

use std::{
    cell::{Cell, UnsafeCell},
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    sync::atomic::Ordering,
};

use uuid::Uuid;

use crate::{allocator::*, loom_testing::*};

const _ONLY_SUPPORTS_64BIT_PLATFORMS: () = assert!(usize::BITS == 64);
const _: () = assert!(MAX_THREADS <= 254);

/// Helper for packing/unpacking atomic lock/generation bits
///
/// - `bits[7:0]` = rwlock
///     - 0 = not locked
///     - !0 = write locked
///     - else contains `n` readers
/// - `bits[62:8]` = generation counter
/// - `bits[63]` = valid (i.e. allocated)
///
/// NOTE: current impl restricts [MAX_THREADS] to never be more than 254
///
/// XXX: The current implementation uses a super dangerous spicy trick
/// that is also technically UB according to the abstract memory model.
/// This lock/generation field is stored at the very beginning of a heap
/// block containing netlist cells/wires, in a location that just so happens
/// to overlap with the heap free list next pointer once the block gets freed.
/// When a block is freed, the allocator will either store null or a valid
/// pointer in this location. Neither of these will have bit 63 set, so
/// we can detect if code tries to acquire a lock to a deleted object
/// (as long as the backing segment itself isn't deleted, which we won't do
/// while any graph algorithms are running).
///
/// FIXME: How does this interact with MTE/PAC?
///
/// NOTE: Generation counters are per-thread and not global. This is fine as it
/// is combined with the address itself in order to reference a specific node
/// (the address will come from different memory segments across different threads)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LockAndGeneration {
    Unallocated {
        _maybe_free_ptr_super_dangerous: u64,
    },
    Unlocked {
        gen: u64,
    },
    WriteLocked {
        gen: u64,
    },
    ReadLocked {
        gen: u64,
        num_readers: u8,
    },
}
impl LockAndGeneration {
    #[inline]
    fn get_gen(self) -> u64 {
        match self {
            LockAndGeneration::Unlocked { gen }
            | LockAndGeneration::WriteLocked { gen }
            | LockAndGeneration::ReadLocked { gen, .. } => gen,
            LockAndGeneration::Unallocated { .. } => unreachable!(),
        }
    }
    #[inline]
    fn get_num_readers(self) -> u8 {
        match self {
            LockAndGeneration::Unlocked { .. } => 0,
            LockAndGeneration::ReadLocked { num_readers, .. } => num_readers,
            LockAndGeneration::WriteLocked { .. } | LockAndGeneration::Unallocated { .. } => {
                // xxx this is a hack for optimizations
                0
            }
        }
    }
}
impl From<u64> for LockAndGeneration {
    #[inline]
    fn from(value: u64) -> Self {
        if value & 0x8000000000000000 == 0 {
            return LockAndGeneration::Unallocated {
                _maybe_free_ptr_super_dangerous: value,
            };
        }
        let rwlock = value & 0xff;
        let gen = (value >> 8) & 0x7fffffffffffff;
        if rwlock == 0 {
            Self::Unlocked { gen }
        } else if rwlock == 0xff {
            Self::WriteLocked { gen }
        } else {
            Self::ReadLocked {
                gen,
                num_readers: rwlock as u8,
            }
        }
    }
}
impl Into<u64> for LockAndGeneration {
    #[inline]
    fn into(self) -> u64 {
        match self {
            LockAndGeneration::Unallocated {
                _maybe_free_ptr_super_dangerous,
            } => {
                debug_assert!(_maybe_free_ptr_super_dangerous <= 0x7fffffffffffffff);
                _maybe_free_ptr_super_dangerous
            }
            LockAndGeneration::Unlocked { gen } => {
                debug_assert!(gen <= 0x7fffffffffffff);
                (gen << 8) | 0x8000000000000000
            }
            LockAndGeneration::WriteLocked { gen } => {
                debug_assert!(gen <= 0x7fffffffffffff);
                (gen << 8) | 0x80000000000000ff
            }
            LockAndGeneration::ReadLocked { gen, num_readers } => {
                debug_assert!(gen <= 0x7fffffffffffff);
                (gen << 8) | (num_readers as u64) | 0x8000000000000000
            }
        }
    }
}

/// Wrapped payload type, additionally containing a rwlock and generation counter
/// (for preventing ABA problem)
#[repr(C)]
#[derive(Debug)]
struct NetlistNodeWithLock<T: Send + Sync> {
    /// R/W lock
    lock_and_generation: AtomicU64,
    /// Inner data
    payload: UnsafeCell<T>,
}
// safety: this is a wrapper for T where we manually enforce the
// shared xor mutable rules using atomics
unsafe impl<T: Send + Sync> Send for NetlistNodeWithLock<T> {}
unsafe impl<T: Send + Sync> Sync for NetlistNodeWithLock<T> {}

/// References to netlist nodes that have a lifetime from a particular heap
///
/// This is basically a fat pointer. It stores a raw pointer and an ABA generation counter.
/// They can be freely copied, sent between threads, etc.
///
/// These items compare with reference equality, not value equality.
pub struct NetlistNodeRef<'arena, T: Send + Sync> {
    ptr: &'arena NetlistNodeWithLock<T>,
    gen: u64,
}
// fixme justify why auto deriving doesn't work
impl<'arena, T: Send + Sync> Clone for NetlistNodeRef<'arena, T> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            gen: self.gen,
        }
    }
}
impl<'arena, T: Send + Sync> Copy for NetlistNodeRef<'arena, T> {}
impl<'arena, T: Send + Sync> Debug for NetlistNodeRef<'arena, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(&format!("NetlistNodeRef<{}>", std::any::type_name::<T>()))
            .field("ptr", &(self.ptr as *const _))
            .field("gen", &self.gen)
            .finish()
    }
}
impl<'arena, T: Send + Sync> PartialEq for NetlistNodeRef<'arena, T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr as *const _ == other.ptr as *const _ && self.gen == other.gen
    }
}
impl<'arena, T: Send + Sync> Eq for NetlistNodeRef<'arena, T> {}
// fixme: do we need/want ord/partialord?
impl<'arena, T: Send + Sync> Hash for NetlistNodeRef<'arena, T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (self.ptr as *const _ as usize).hash(state);
        self.gen.hash(state);
    }
}

/// Guard object holding exclusive access to a graph node (allowing reads and writes)
pub struct NetlistNodeWriteGuard<'shard, 'arena, T: Send + Sync> {
    /// Object that this guard is protecting
    pub p: NetlistNodeRef<'arena, T>,
    /// Prevent this type from being `Sync`
    _pd1: PhantomData<UnsafeCell<()>>,
    /// Prevent this type from outliving thread shard
    ///
    /// Note that there is no safety reason why this is necessary *at this layer of abstraction*.
    /// Locked objects can be unlocked from any thread without issue.
    /// In fact, the "Galois system" inspired algorithm executor
    /// can end up transferring guards across threads.
    ///
    /// The purpose of this is to enforce that, when a [SlabRootGlobalGuard] is held,
    /// not only is there no _allocator_ traffic occurring, but there is *also*
    /// no activity happening _within_ the netlist itself.
    /// (Imagine otherwise a situation where *all* thread shards are dropped, so
    /// nobody can allocate or free everything, but a bunch of threads are running
    /// in the background mutating the existing netlist.)
    _pd2: PhantomData<&'shard ()>,
}
impl<'shard, 'arena, T: Send + Sync> NetlistNodeWriteGuard<'shard, 'arena, T> {
    /// Downgrades read/write access to read-only access
    ///
    /// This will allow other readers to potentially start accessing
    /// the new data that was written
    pub fn downgrade(self) -> NetlistNodeReadGuard<'shard, 'arena, T> {
        // we have exclusive access
        // we can freely downgrade to a read lock with a single reader
        // we *do* need other threads trying to acquire read locks
        // to see data we wrote (synchronizes-with)
        // so we need release ordering
        // we become read-only to the current thread afterwards,
        // so the current thread cannot have any writes afterwards
        // that can be reordered. it *can* have reads afterwards, but those
        // reads must read data that *we* wrote. so we don't need acquire
        let old_atomic_val = self
            .p
            .ptr
            .lock_and_generation
            .fetch_and(!0xfe, Ordering::Release);
        debug_assert_eq!(
            LockAndGeneration::from(old_atomic_val),
            LockAndGeneration::WriteLocked { gen: self.p.gen }
        );
        let p = self.p;
        mem::forget(self);
        NetlistNodeReadGuard {
            p,
            _pd1: PhantomData,
            _pd2: PhantomData,
        }
    }
}
impl<'shard, 'arena, T: Send + Sync> Debug for NetlistNodeWriteGuard<'shard, 'arena, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple(&format!(
            "NetlistNodeWriteGuard<{}>",
            std::any::type_name::<T>()
        ))
        .field(&self.p)
        .finish()
    }
}
impl<'shard, 'arena, T: Send + Sync> Deref for NetlistNodeWriteGuard<'shard, 'arena, T> {
    type Target = T;

    fn deref<'guard>(&'guard self) -> &'guard T {
        unsafe {
            // safety: only one write guard can exist
            &*self.p.ptr.payload.get()
        }
    }
}
impl<'shard, 'arena, T: Send + Sync> DerefMut for NetlistNodeWriteGuard<'shard, 'arena, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            // safety: only one write guard can exist
            &mut *self.p.ptr.payload.get()
        }
    }
}
impl<'shard, 'arena, T: Send + Sync> Drop for NetlistNodeWriteGuard<'shard, 'arena, T> {
    fn drop<'guard>(&'guard mut self) {
        // we have exclusive access
        // we need to push out all previous memory accesses
        // and establish synchronizes-with trying to get access
        let old_atomic_val = self
            .p
            .ptr
            .lock_and_generation
            .fetch_and(!0xff, Ordering::Release);
        debug_assert_eq!(
            LockAndGeneration::from(old_atomic_val),
            LockAndGeneration::WriteLocked { gen: self.p.gen }
        )
    }
}

/// Guard object holding read-only access to a graph node (allowing multiple readers)
pub struct NetlistNodeReadGuard<'shard, 'arena, T: Send + Sync> {
    /// Object that this guard is protecting
    pub p: NetlistNodeRef<'arena, T>,
    /// Prevent this type from being `Sync`
    _pd1: PhantomData<UnsafeCell<()>>,
    /// Prevent this type from outliving thread shard
    ///
    /// See note under [NetlistNodeWriteGuard::_pd2]
    _pd2: PhantomData<&'shard ()>,
}
impl<'shard, 'arena, T: Send + Sync> NetlistNodeReadGuard<'shard, 'arena, T> {
    /// Try to convert read-only access to exclusive read/write access
    ///
    /// If this thread happens to be the only reader accessing the node,
    /// access will be upgraded to an exclusive read/write lock.
    ///
    /// If upgrading fails, returns with a read/only lock still held.
    pub fn try_upgrade(
        self,
    ) -> Result<NetlistNodeWriteGuard<'shard, 'arena, T>, NetlistNodeReadGuard<'shard, 'arena, T>>
    {
        let mut old_atomic_val = self.p.ptr.lock_and_generation.load(Ordering::Relaxed);
        loop {
            let old_atomic = LockAndGeneration::from(old_atomic_val);
            debug_assert!(matches!(
                old_atomic,
                LockAndGeneration::ReadLocked { gen, .. } if gen == self.p.gen
            ));
            debug_assert!(old_atomic.get_num_readers() >= 1);
            if old_atomic.get_num_readers() > 1 {
                // failed to claim
                return Err(self);
            }
            // else try to acquire
            let new_atomic_val = old_atomic_val | 0xff;
            match self.p.ptr.lock_and_generation.compare_exchange_weak(
                old_atomic_val,
                new_atomic_val,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    let p = self.p;
                    mem::forget(self);
                    return Ok(NetlistNodeWriteGuard {
                        p,
                        _pd1: PhantomData,
                        _pd2: PhantomData,
                    });
                }
                Err(x) => old_atomic_val = x,
            }
        }
    }
}
impl<'shard, 'arena, T: Send + Sync> Debug for NetlistNodeReadGuard<'shard, 'arena, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple(&format!(
            "NetlistNodeReadGuard<{}>",
            std::any::type_name::<T>()
        ))
        .field(&self.p)
        .finish()
    }
}
impl<'shard, 'arena, T: Send + Sync> Deref for NetlistNodeReadGuard<'shard, 'arena, T> {
    type Target = T;

    fn deref<'guard>(&'guard self) -> &'guard T {
        unsafe {
            // safety: no way to get a &mut when read guards exist
            &*self.p.ptr.payload.get()
        }
    }
}
impl<'shard, 'arena, T: Send + Sync> Drop for NetlistNodeReadGuard<'shard, 'arena, T> {
    fn drop<'guard>(&'guard mut self) {
        // ordering: in order to prevent reads to data from moving
        // after this atomic update, we *still* need release ordering
        // (even though no data is modified)
        let old_atomic_val = self
            .p
            .ptr
            .lock_and_generation
            .fetch_sub(1, Ordering::Release);
        debug_assert!(matches!(
            LockAndGeneration::from(old_atomic_val),
            LockAndGeneration::ReadLocked { gen, .. } if gen == self.p.gen
        ));
    }
}

/// Cells in a netlist
#[derive(Debug)]
pub struct NetlistCell<'arena> {
    // todo
    cell_type: Uuid,
    debug_id: usize,
    visited_marker: bool,
    connections: Vec<Option<NetlistWireRef<'arena>>>,
}
pub type NetlistCellRef<'arena> = NetlistNodeRef<'arena, NetlistCell<'arena>>;
pub type NetlistCellWriteGuard<'shard, 'arena> =
    NetlistNodeWriteGuard<'shard, 'arena, NetlistCell<'arena>>;
pub type NetlistCellReadGuard<'shard, 'arena> =
    NetlistNodeReadGuard<'shard, 'arena, NetlistCell<'arena>>;
impl<'arena> NetlistCell<'arena> {
    pub unsafe fn init(
        self_: *mut Self,
        cell_type: Uuid,
        debug_id: usize,
        num_connections: usize,
    ) -> &'arena mut Self {
        (*self_).cell_type = cell_type;
        (*self_).debug_id = debug_id;
        (*self_).visited_marker = false;
        (*self_).connections = vec![None; num_connections];

        // safety: assert that we initialized everything
        &mut *self_
    }
}

/// Wires in a netlist
#[derive(Debug)]
pub struct NetlistWire<'arena> {
    // todo
    debug_id: usize,
    drivers: Vec<NetlistCellRef<'arena>>,
    sinks: Vec<NetlistCellRef<'arena>>,
    bidirs: Vec<NetlistCellRef<'arena>>,
}
pub type NetlistWireRef<'arena> = NetlistNodeRef<'arena, NetlistWire<'arena>>;
pub type NetlistWireWriteGuard<'shard, 'arena> =
    NetlistNodeWriteGuard<'shard, 'arena, NetlistWire<'arena>>;
pub type NetlistWireReadGuard<'shard, 'arena> =
    NetlistNodeReadGuard<'shard, 'arena, NetlistWire<'arena>>;
impl<'arena> NetlistWire<'arena> {
    pub unsafe fn init(self_: *mut Self, debug_id: usize) -> &'arena mut Self {
        (*self_).debug_id = debug_id;
        (*self_).drivers = Vec::new();
        (*self_).sinks = Vec::new();
        (*self_).bidirs = Vec::new();

        // safety: assert that we initialized everything
        &mut *self_
    }
}

/// Top-level netlist data structure
#[derive(Debug)]
pub struct NetlistModule<'arena> {
    heap: SlabRoot<
        'arena,
        NetlistNodeWithLock<NetlistCell<'arena>>,
        NetlistNodeWithLock<NetlistWire<'arena>>,
    >,
}

impl<'arena> NetlistModule<'arena> {
    /// Construct a new netlist
    pub fn new() -> Self {
        Self {
            heap: SlabRoot::new(),
        }
    }
    /// Get a thread shard for performing operations on the netlist
    pub fn new_thread(&'arena self) -> NetlistModuleThreadAccessor<'arena> {
        NetlistModuleThreadAccessor {
            heap_shard: self.heap.new_thread(),
            debug_id: Cell::new(0),
        }
    }
}

/// Provides one thread with access to the netlist
#[derive(Debug)]
pub struct NetlistModuleThreadAccessor<'arena> {
    heap_shard: SlabThreadShard<
        'arena,
        NetlistNodeWithLock<NetlistCell<'arena>>,
        NetlistNodeWithLock<NetlistWire<'arena>>,
    >,
    debug_id: Cell<usize>,
}

impl<'arena> NetlistModuleThreadAccessor<'arena> {
    /// Add a new netlist cell
    pub fn new_cell<'wrapper>(
        &'wrapper self,
        cell_type: Uuid,
        num_connections: usize,
    ) -> NetlistCellWriteGuard<'wrapper, 'arena> {
        let (new_obj, gen) = self.heap_shard.alloc_netlist_cell();
        unsafe {
            // fixme: wtf have we made any rust UB anywhere?
            let maybe_uninit = &*new_obj.alloced;
            let new_obj_ptr = maybe_uninit.as_ptr();
            // at this point, the memory allocator has established enough of a
            // synchronizes-with a potential remote freeing thread
            // that we can safely reuse the memory block
            //
            // the potential concern to think about is
            // replacing pointers elsewhere in the netlist
            // with a pointer (w/ new generation) to this block,
            // and whether or not that can end up reordering with
            // the following store here, and whether or not that can cause problems
            //
            // in order to replace a pointer elsewhere in the netlist,
            // we have to have a write lock on it. this means that
            // no other thread can have a read guard on it
            // until after we drop the write guard (R^W enforced logically).
            // when we finally do drop the write guard, and another thread
            // picks up a read guard to that same *other* node
            // (not this one being allocated here), then a
            // synchronizes-with is established via *that* node's lock_and_generation.
            // at that point, *everything* that happens-before
            // the dropping of the write guard (which includes
            // *everything* sequenced-before, which includes both
            // the pointer replacement *and* this following store)
            // are *all* visible to the other thread
            //
            // tl;dr in order for another thread to even be allowed to *see*
            // the new pointer we are about to return, we have guaranteed
            // that this following store is also visible
            (*new_obj_ptr).lock_and_generation.store(
                LockAndGeneration::WriteLocked { gen }.into(),
                Ordering::Relaxed,
            );
            NetlistCell::init(
                (*new_obj_ptr).payload.get(),
                cell_type,
                self.debug_id.get(),
                num_connections,
            );
            self.debug_id.set(self.debug_id.get() + 1);

            NetlistCellWriteGuard {
                p: NetlistCellRef {
                    ptr: maybe_uninit.assume_init_ref(),
                    gen,
                },
                _pd1: PhantomData,
                _pd2: PhantomData,
            }
        }
    }

    /// Add a new netlist wire
    pub fn new_wire<'wrapper>(&'wrapper self) -> NetlistWireWriteGuard<'wrapper, 'arena> {
        let (new_obj, gen) = self.heap_shard.alloc_netlist_wire();
        unsafe {
            // fixme: wtf have we made any rust UB anywhere?
            let maybe_uninit = &*new_obj.alloced;
            let new_obj_ptr = maybe_uninit.as_ptr();
            // see notes above
            (*new_obj_ptr).lock_and_generation.store(
                LockAndGeneration::WriteLocked { gen }.into(),
                Ordering::Relaxed,
            );
            NetlistWire::init((*new_obj_ptr).payload.get(), self.debug_id.get());
            self.debug_id.set(self.debug_id.get() + 1);

            NetlistWireWriteGuard {
                p: NetlistWireRef {
                    ptr: maybe_uninit.assume_init_ref(),
                    gen,
                },
                _pd1: PhantomData,
                _pd2: PhantomData,
            }
        }
    }

    /// Delete a netlist cell
    ///
    /// Deletion is only permitted if the caller has exclusive write access to the node,
    /// which is enforced by consuming the write guard
    pub fn delete_cell<'wrapper>(&'wrapper self, cell: NetlistCellWriteGuard<'wrapper, 'arena>) {
        // XXX we currently have a (unfixable in the current design) source of UB
        // when deallocating: no matter what we do with lock_and_generation here,
        // the allocator itself will write a ->next pointer without using atomic ops.
        // this should be fine in practice, as it's an aligned pointer store.

        // there are two memory ordering concerns involving the payload when we are freeing:
        // * another thread reusing the memory for something else
        // * another thread trying to lock-for-r/w the deleted entry

        // in the first case, *within the allocator itself* there is a synchronizes-with
        // relation on the page/thread remote free list pointer access.
        // all the crap that we did on the payload (that we no longer care about, since we're freeing)
        // as well as all the free list manipulation that the allocator does
        // happens-before the new thread does any kind of setup of its new payload

        // in the second case, we *never* manage to establish a synchronizes-with relation
        // (even if we assume that the allocator free list manipulation is a relaxed atomic store instead of UB)
        // however, each atomic variable does have a total order to modifications
        // specific to it. this means that, once we invalidate the generation counter,
        // other threads won't ever be able to successfully acquire a read lock
        // (either they already notice it's invalid when doing a relaxed load, or else CAS will fail)
        // so we should be fine in practice, even though we are UB by the formal model

        // just in case, we *should* invalidate the marker ourselves
        // (rather than depend on the allocator to do it).
        // we don't need to guarantee any memory ordering ourselves
        // (what the allocator does is sufficient)
        cell.p.ptr.lock_and_generation.store(0, Ordering::Relaxed);
        unsafe {
            // safety: just coercing between repr(C) union references
            self.heap_shard
                .free_netlist_cell(mem::transmute(cell.p.ptr))
        }
        mem::forget(cell);
    }

    /// Delete a netlist wire
    ///
    /// Deletion is only permitted if the caller has exclusive write access to the node,
    /// which is enforced by consuming the write guard
    pub fn delete_wire<'wrapper>(&'wrapper self, wire: NetlistWireWriteGuard<'wrapper, 'arena>) {
        // see notes above
        wire.p.ptr.lock_and_generation.store(0, Ordering::Relaxed);
        unsafe {
            // safety: just coercing between repr(C) union references
            self.heap_shard
                .free_netlist_wire(mem::transmute(wire.p.ptr))
        }
        mem::forget(wire);
    }

    /// Try to acquire read-only access to a graph node
    ///
    /// Return values:
    /// * `Err(())` -> this object has been deleted (it is definitely gone, do not try again)
    /// * `Ok(None)` -> lock acquiring failed (contention, can try again)
    /// * `Ok(_)` -> acquire succeeded
    pub fn try_read<'wrapper, CellOrWireTy: Send + Sync>(
        &'wrapper self,
        p: NetlistNodeRef<'arena, CellOrWireTy>,
    ) -> Result<Option<NetlistNodeReadGuard<'wrapper, 'arena, CellOrWireTy>>, ()> {
        let mut old_atomic_val = p.ptr.lock_and_generation.load(Ordering::Relaxed);
        loop {
            let old_atomic = LockAndGeneration::from(old_atomic_val);
            if let LockAndGeneration::Unallocated { .. } = old_atomic {
                // object invalidated (gone, deleted)
                return Err(());
            }
            if old_atomic.get_gen() != p.gen {
                // object invalidated (gone, deleted)
                return Err(());
            }
            if let LockAndGeneration::WriteLocked { .. } = old_atomic {
                // failed to claim
                return Ok(None);
            }
            // else try to acquire
            debug_assert!(old_atomic.get_num_readers() != 254);
            let new_atomic_val = old_atomic_val + 1;
            match p.ptr.lock_and_generation.compare_exchange_weak(
                old_atomic_val,
                new_atomic_val,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    return Ok(Some(NetlistNodeReadGuard {
                        p,
                        _pd1: PhantomData,
                        _pd2: PhantomData,
                    }));
                }
                Err(x) => old_atomic_val = x,
            }
        }
    }

    /// Try to acquire exclusive read/write access to a graph node
    ///
    /// Return values:
    /// * `Err(())` -> this object has been deleted (it is definitely gone, do not try again)
    /// * `Ok(None)` -> lock acquiring failed (contention, can try again)
    /// * `Ok(_)` -> acquire succeeded
    pub fn try_write<'wrapper, CellOrWireTy: Send + Sync>(
        &'wrapper self,
        p: NetlistNodeRef<'arena, CellOrWireTy>,
    ) -> Result<Option<NetlistNodeWriteGuard<'wrapper, 'arena, CellOrWireTy>>, ()> {
        let mut old_atomic_val = p.ptr.lock_and_generation.load(Ordering::Relaxed);
        loop {
            let old_atomic = LockAndGeneration::from(old_atomic_val);
            if let LockAndGeneration::Unallocated { .. } = old_atomic {
                // object invalidated (gone, deleted)
                return Err(());
            }
            if old_atomic.get_gen() != p.gen {
                // object invalidated (gone, deleted)
                return Err(());
            }
            if let LockAndGeneration::WriteLocked { .. } | LockAndGeneration::ReadLocked { .. } =
                old_atomic
            {
                // failed to claim
                return Ok(None);
            }
            // else try to acquire
            let new_atomic_val = old_atomic_val | 0xff;
            match p.ptr.lock_and_generation.compare_exchange_weak(
                old_atomic_val,
                new_atomic_val,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    return Ok(Some(NetlistNodeWriteGuard {
                        p,
                        _pd1: PhantomData,
                        _pd2: PhantomData,
                    }))
                }
                Err(x) => old_atomic_val = x,
            }
        }
    }
}

pub fn connect_driver<'guard, 'thread, 'arena>(
    cell: &'guard mut NetlistCellWriteGuard<'thread, 'arena>,
    conn_idx: usize,
    wire: &'guard mut NetlistWireWriteGuard<'thread, 'arena>,
) {
    cell.connections[conn_idx] = Some(wire.p);
    wire.drivers.push(cell.p);
}

pub fn connect_sink<'guard, 'thread, 'arena>(
    cell: &'guard mut NetlistCellWriteGuard<'thread, 'arena>,
    conn_idx: usize,
    wire: &'guard mut NetlistWireWriteGuard<'thread, 'arena>,
) {
    cell.connections[conn_idx] = Some(wire.p);
    wire.sinks.push(cell.p);
}

pub fn connect_bidir<'guard, 'thread, 'arena>(
    cell: &'guard mut NetlistCellWriteGuard<'thread, 'arena>,
    conn_idx: usize,
    wire: &'guard mut NetlistWireWriteGuard<'thread, 'arena>,
) {
    cell.connections[conn_idx] = Some(wire.p);
    wire.bidirs.push(cell.p);
}

pub fn disconnect_driver<'guard, 'thread, 'arena>(
    cell: &'guard mut NetlistCellWriteGuard<'thread, 'arena>,
    conn_idx: usize,
    wire: &'guard mut NetlistWireWriteGuard<'thread, 'arena>,
) {
    let ref_wire_idx = cell.connections[conn_idx].take();
    assert_eq!(ref_wire_idx, Some(wire.p));
    let wire_to_cell_idx = wire
        .drivers
        .iter()
        .position(|wire_to_cell| cell.p == *wire_to_cell)
        .unwrap();
    wire.drivers.swap_remove(wire_to_cell_idx);
}

pub fn disconnect_sink<'guard, 'thread, 'arena>(
    cell: &'guard mut NetlistCellWriteGuard<'thread, 'arena>,
    conn_idx: usize,
    wire: &'guard mut NetlistWireWriteGuard<'thread, 'arena>,
) {
    let ref_wire_idx = cell.connections[conn_idx].take();
    assert_eq!(ref_wire_idx, Some(wire.p));
    let wire_to_cell_idx = wire
        .sinks
        .iter()
        .position(|wire_to_cell| cell.p == *wire_to_cell)
        .unwrap();
    wire.drivers.swap_remove(wire_to_cell_idx);
}

pub fn disconnect_bidir<'guard, 'thread, 'arena>(
    cell: &'guard mut NetlistCellWriteGuard<'thread, 'arena>,
    conn_idx: usize,
    wire: &'guard mut NetlistWireWriteGuard<'thread, 'arena>,
) {
    let ref_wire_idx = cell.connections[conn_idx].take();
    assert_eq!(ref_wire_idx, Some(wire.p));
    let wire_to_cell_idx = wire
        .bidirs
        .iter()
        .position(|wire_to_cell| cell.p == *wire_to_cell)
        .unwrap();
    wire.drivers.swap_remove(wire_to_cell_idx);
}

#[cfg(test)]
mod tests {
    use std::thread;
    use std::time::Instant;

    use super::*;

    use memory_stats::memory_stats;
    use rand::Rng;
    use rand::SeedableRng;
    use uuid::uuid;

    const TEST_LUT_UUID: Uuid = uuid!("00000000-0000-0000-0000-000000000000");
    const TEST_BUF_UUID: Uuid = uuid!("00000000-0000-0000-0000-000000000001");

    #[test]
    fn netlist_locking_smoke_test() {
        let netlist = NetlistModule::new();
        let thread = netlist.new_thread();

        let mut cell_0 = thread.new_cell(TEST_LUT_UUID, 1);
        println!("Allocated new cell, {:?}", cell_0.p);

        let mut wire_0 = thread.new_wire();
        println!("Allocated new wire, {:?}", wire_0.p);

        connect_driver(&mut cell_0, 0, &mut wire_0);

        let cell_0_p = cell_0.p;
        let wire_0_p = wire_0.p;

        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x80000000000000ff
        );
        assert_eq!(
            wire_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x80000000000000ff
        );

        // shouldn't be possible to get any read guards
        let try_read = thread.try_read(cell_0_p);
        assert!(try_read.is_ok());
        assert!(try_read.unwrap().is_none());
        let try_read = thread.try_read(wire_0_p);
        assert!(try_read.is_ok());
        assert!(try_read.unwrap().is_none());

        drop(cell_0);
        drop(wire_0);

        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000000
        );
        assert_eq!(
            wire_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000000
        );

        let cell_0_r_0 = thread.try_read(cell_0_p).unwrap().unwrap();
        let wire_0_r_0 = thread.try_read(wire_0_p).unwrap().unwrap();

        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000001
        );
        assert_eq!(
            wire_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000001
        );

        println!("Re-reading cell: {:?}", *cell_0_r_0);
        println!("Re-reading wire: {:?}", *wire_0_r_0);

        assert_eq!(cell_0_r_0.connections[0], Some(wire_0_p));
        assert_eq!(wire_0_r_0.drivers[0], cell_0_p);

        let cell_0_r_1 = thread.try_read(cell_0_p).unwrap().unwrap();
        let wire_0_r_1 = thread.try_read(wire_0_p).unwrap().unwrap();

        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000002
        );
        assert_eq!(
            wire_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000002
        );

        println!("Re-reading cell again: {:?}", *cell_0_r_1);
        println!("Re-reading wire again: {:?}", *wire_0_r_1);

        assert_eq!(cell_0_r_1.connections[0], Some(wire_0_p));
        assert_eq!(wire_0_r_1.drivers[0], cell_0_p);

        let try_write = thread.try_write(cell_0_p);
        assert!(try_write.is_ok());
        assert!(try_write.unwrap().is_none());
        let try_write = thread.try_write(wire_0_p);
        assert!(try_write.is_ok());
        assert!(try_write.unwrap().is_none());

        drop(cell_0_r_0);
        drop(wire_0_r_1);

        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000001
        );
        assert_eq!(
            wire_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000001
        );

        let try_write = thread.try_write(cell_0_p);
        assert!(try_write.is_ok());
        assert!(try_write.unwrap().is_none());
        let try_write = thread.try_write(wire_0_p);
        assert!(try_write.is_ok());
        assert!(try_write.unwrap().is_none());

        drop(cell_0_r_1);
        drop(wire_0_r_0);

        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000000
        );
        assert_eq!(
            wire_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000000
        );

        let cell_0_re_w = thread.try_write(cell_0_p).unwrap().unwrap();
        let wire_0_re_w = thread.try_write(wire_0_p).unwrap().unwrap();

        println!("Re-reading cell again through write: {:?}", *cell_0_re_w);
        println!("Re-reading wire again through write: {:?}", *wire_0_re_w);

        assert_eq!(cell_0_re_w.connections[0], Some(wire_0_p));
        assert_eq!(wire_0_re_w.drivers[0], cell_0_p);

        thread.delete_cell(cell_0_re_w);

        // xxx reading "freed" memory!
        assert_eq!(cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst), 0);

        assert!(thread.try_write(cell_0_p).is_err());
        assert!(thread.try_read(cell_0_p).is_err());

        thread.delete_wire(wire_0_re_w);

        // xxx reading "freed" memory!
        assert_eq!(wire_0_p.ptr.lock_and_generation.load(Ordering::SeqCst), 0);

        assert!(thread.try_write(wire_0_p).is_err());
        assert!(thread.try_read(wire_0_p).is_err());
    }

    #[test]
    fn netlist_locking_smoke_test_generation() {
        let netlist = NetlistModule::new();
        let thread = netlist.new_thread();

        let cell_0 = thread.new_cell(TEST_LUT_UUID, 0);
        let cell_0_p = cell_0.p;
        println!("Allocated new cell, {:?}", cell_0_p);
        thread.delete_cell(cell_0);

        let mut num_iters = 0;

        loop {
            let cell_i = thread.new_cell(TEST_LUT_UUID, 0);
            let cell_i_p = cell_i.p;
            if cell_0_p.ptr as *const _ == cell_i_p.ptr {
                println!("Reused pointer detected after {} iters", num_iters);
                dbg!(cell_0_p);
                dbg!(cell_i_p);
                assert_ne!(cell_0_p.gen, cell_i_p.gen);

                assert!(thread.try_read(cell_0_p).is_err());
                assert!(thread.try_write(cell_0_p).is_err());

                break;
            }
            thread.delete_cell(cell_i);
            num_iters += 1;
        }
    }

    #[test]
    fn netlist_locking_smoke_test_upgrade_downgrade() {
        let netlist = NetlistModule::new();
        let thread = netlist.new_thread();

        let cell_0 = thread.new_cell(TEST_LUT_UUID, 0);
        let cell_0_p = cell_0.p;
        println!("Allocated new cell, {:?}", cell_0_p);

        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x80000000000000ff
        );

        let cell_0_r_0 = cell_0.downgrade();
        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000001
        );

        let cell_0_r_1 = thread.try_read(cell_0_p).unwrap().unwrap();
        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000002
        );

        // note: drops
        assert!(cell_0_r_0.try_upgrade().is_err());
        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000001
        );

        let cell_0_w_again = cell_0_r_1.try_upgrade().unwrap();
        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x80000000000000ff
        );

        drop(cell_0_w_again);
        assert_eq!(
            cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst),
            0x8000000000000000
        );
    }

    #[test]
    #[ignore = "not automated, human eye verified"]
    fn netlist_locking_debug_tests() {
        let netlist = NetlistModule::new();
        dbg!(&netlist);
        let thread = netlist.new_thread();
        dbg!(&thread);

        let cell_0 = thread.new_cell(TEST_LUT_UUID, 0);
        dbg!(&cell_0);
        dbg!(&*cell_0);
    }

    #[test]
    fn bench_full_custom_netlist() {
        const NLUTS: usize = 1_000_000;
        const AVG_FANIN: f64 = 3.0;
        const N_INITIAL_WORK: usize = 1000;
        const NTHREADS: usize = 6;

        // FIXME
        let netlist = &*Box::leak(Box::new(NetlistModule::new()));
        let init_thread_shard = netlist.new_thread();
        let mut rng = rand_xorshift::XorShiftRng::seed_from_u64(0);

        let start_create = Instant::now();
        let start_mem = memory_stats().unwrap();
        let mut generate_hax_luts_vec = Vec::new();
        let mut generate_hax_wires_vec = Vec::new();
        for _ in 0..NLUTS {
            let mut lut = init_thread_shard.new_cell(TEST_LUT_UUID, 5);
            let mut outwire = init_thread_shard.new_wire();
            connect_driver(&mut lut, 4, &mut outwire);
            generate_hax_luts_vec.push(lut);
            generate_hax_wires_vec.push(outwire);
        }
        for luti in 0..NLUTS {
            let lut = &mut generate_hax_luts_vec[luti];
            for inpi in 0..4 {
                if rng.gen::<f64>() < (AVG_FANIN / 4.0) {
                    let inp_wire_i = rng.gen_range(0..NLUTS);
                    let inp_wire = &mut generate_hax_wires_vec[inp_wire_i];
                    connect_sink(lut, inpi, inp_wire);
                }
            }
        }
        let create_duration = start_create.elapsed();
        let create_mem = memory_stats().unwrap();
        println!("Creating netlist took {:?}", create_duration);
        println!(
            "Creating netlist took {:?} MB memory",
            (create_mem.physical_mem - start_mem.physical_mem) as f64 / 1024.0 / 1024.0
        );

        let workqueue = work_queue::Queue::new(NTHREADS, 128);
        {
            for _ in 0..N_INITIAL_WORK {
                let luti = rng.gen_range(0..NLUTS);
                let lut = generate_hax_luts_vec[luti].p;
                // println!("Initial work item: {}", luti);
                workqueue.push(lut);
            }
        }

        drop(generate_hax_luts_vec);
        drop(generate_hax_wires_vec);
        drop(init_thread_shard);

        let start_mutate = Instant::now();
        let thread_handles = workqueue
            .local_queues()
            .map(|mut local_queue| {
                let netlist_thread_shard = netlist.new_thread();
                thread::spawn(move || {
                    while let Some(cell) = local_queue.pop() {
                        let cell_w = netlist_thread_shard.try_write(cell).unwrap();
                        if cell_w.is_none() {
                            // dbg!("failed to grab self");
                            local_queue.push(cell);
                            continue;
                        }
                        let mut cell_w = cell_w.unwrap();
                        // println!("grabbed cell {}", cell_w.debug_id);
                        if cell_w.visited_marker {
                            continue;
                        }

                        if cell_w.cell_type == TEST_BUF_UUID {
                            let inp_wire_i = cell_w.connections[0].unwrap();
                            let inp_wire_r = netlist_thread_shard.try_read(inp_wire_i).unwrap();
                            if inp_wire_r.is_none() {
                                // dbg!("failed to grab inp wire for buf");
                                local_queue.push(cell);
                                continue;
                            }
                            let inp_wire_r = inp_wire_r.unwrap();
                            let driver_cell = inp_wire_r.drivers[0];

                            cell_w.visited_marker = true;
                            local_queue.push(driver_cell);
                        } else {
                            // wtf

                            // hack for self-loop
                            let outwire = cell_w.connections[4].unwrap();

                            // grab input wires for read
                            let mut inp_wire_rs = [None, None, None, None];
                            for inp_i in 0..4 {
                                if let Some(inp_wire_ref) = cell_w.connections[inp_i] {
                                    if inp_wire_ref != outwire {
                                        let inp_wire_r =
                                            netlist_thread_shard.try_read(inp_wire_ref).unwrap();
                                        if inp_wire_r.is_none() {
                                            // dbg!("failed to grab inp {}", inp_i);
                                            local_queue.push(cell);
                                            continue;
                                        }
                                        let inp_wire_r = inp_wire_r.unwrap();
                                        // println!("grabbed wire {}", inp_wire_r.debug_id);
                                        inp_wire_rs[inp_i] = Some(inp_wire_r);
                                    }
                                }
                            }

                            // grab output wire for write
                            let outwire_w = netlist_thread_shard.try_write(outwire).unwrap();
                            if outwire_w.is_none() {
                                // dbg!("failed to grab outp");
                                local_queue.push(cell);
                                continue;
                            }
                            let mut outwire_w = outwire_w.unwrap();

                            let mut added_buf = netlist_thread_shard.new_cell(TEST_BUF_UUID, 2);
                            let mut added_wire = netlist_thread_shard.new_wire();

                            // actual updates
                            cell_w.visited_marker = true;

                            for inp_wire_r in &inp_wire_rs {
                                if let Some(inp_wire_r) = inp_wire_r {
                                    local_queue.push(inp_wire_r.drivers[0]);
                                }
                            }

                            // xxx this is an ad-hoc clusterfuck
                            let outwire_backlink_idx = outwire_w
                                .drivers
                                .iter()
                                .position(|wire_to_cell| cell == *wire_to_cell)
                                .unwrap();

                            outwire_w.drivers[outwire_backlink_idx] = added_buf.p;
                            added_buf.connections[1] = Some(outwire);

                            added_buf.connections[0] = Some(added_wire.p);
                            added_wire.sinks.push(added_buf.p);

                            cell_w.connections[4] = Some(added_wire.p);
                            added_wire.drivers.push(cell);
                        }
                    }
                })
            })
            .collect::<Vec<_>>();

        for t in thread_handles {
            t.join().unwrap();
        }
        let mutate_duration = start_mutate.elapsed();
        let mutate_ram = memory_stats().unwrap();
        println!("Mutating netlist took {:?}", mutate_duration);
        println!(
            "Final additional usage {:?} MB memory",
            (mutate_ram.physical_mem - start_mem.physical_mem) as f64 / 1024.0 / 1024.0
        );
    }
}
