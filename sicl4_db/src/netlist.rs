//! Core of the custom netlist data structure
//!
//! This contains logic for managing locks on netlist nodes

use std::{
    cell::UnsafeCell,
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    sync::atomic::Ordering,
};

use crate::{allocator::*, loom_testing::*};

const _ONLY_SUPPORTS_64BIT_PLATFORMS: () = assert!(usize::BITS == 64);
const _: () = assert!(crate::allocator::MAX_THREADS <= 254);

/// - `bits[7:0]` = rwlock
///     - 0 = not locked
///     - !0 = write locked
///     - else contains `n` readers
/// - `bits[62:8]` = generation counter
/// - `bits[63]` = valid
// NOTE: current impl restricts MAX_THREADS to never be more than 254
// super dangerous spicy trick: the high bit is used to indicate that this
// memory block contains valid, allocated data.
// this will be used for implementing "search through heap, in any order"
// the reason that this works is because blocks on a free list
// will contain a pointer which overlaps this field.
// this pointer is either null or a valid address,
// which cannot have the high bit set on all platforms we care about
//
// the generation counter can indeed be per-thread, as it is combined with
// the address itself (which will be from different segments across different threads)
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
                unreachable!()
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
/// Stores a raw pointer and an ABA generation counter
pub struct NetlistNodeRef<'arena, T: Send + Sync> {
    ptr: &'arena NetlistNodeWithLock<T>,
    gen: u64,
}
// these fat references can be freely copied just like a normal reference
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
// Err(()) -> wrong generation (obj doesn't exist anymore)
// Ok(None) -> acquire failed
// Ok(x) -> acquire succeeded
impl<'arena, T: Send + Sync> NetlistNodeRef<'arena, T> {
    pub fn try_write(self) -> Result<Option<NetlistNodeWriteGuard<'arena, T>>, ()> {
        let mut old_atomic_val = self.ptr.lock_and_generation.load(Ordering::Relaxed);
        loop {
            let old_atomic = LockAndGeneration::from(old_atomic_val);
            if let LockAndGeneration::Unallocated { .. } = old_atomic {
                // object invalidated (gone, deleted)
                return Err(());
            }
            if old_atomic.get_gen() != self.gen {
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
            match self.ptr.lock_and_generation.compare_exchange_weak(
                old_atomic_val,
                new_atomic_val,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    return Ok(Some(NetlistNodeWriteGuard {
                        p: self,
                        _pd: PhantomData,
                    }))
                }
                Err(x) => old_atomic_val = x,
            }
        }
    }

    pub fn try_read(self) -> Result<Option<NetlistNodeReadGuard<'arena, T>>, ()> {
        let mut old_atomic_val = self.ptr.lock_and_generation.load(Ordering::Relaxed);
        loop {
            let old_atomic = LockAndGeneration::from(old_atomic_val);
            if let LockAndGeneration::Unallocated { .. } = old_atomic {
                // object invalidated (gone, deleted)
                return Err(());
            }
            if old_atomic.get_gen() != self.gen {
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
            match self.ptr.lock_and_generation.compare_exchange_weak(
                old_atomic_val,
                new_atomic_val,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    return Ok(Some(NetlistNodeReadGuard {
                        p: self,
                        _pd: PhantomData,
                    }));
                }
                Err(x) => old_atomic_val = x,
            }
        }
    }
}

pub struct NetlistNodeWriteGuard<'arena, T: Send + Sync> {
    pub p: NetlistNodeRef<'arena, T>,
    /// prevent this type from being `Sync`
    _pd: PhantomData<UnsafeCell<()>>,
}
impl<'arena, T: Send + Sync> Deref for NetlistNodeWriteGuard<'arena, T> {
    type Target = T;

    fn deref<'guard>(&'guard self) -> &'guard T {
        unsafe {
            // safety: only one write guard can exist
            &*self.p.ptr.payload.get()
        }
    }
}
impl<'arena, T: Send + Sync> DerefMut for NetlistNodeWriteGuard<'arena, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            // safety: only one write guard can exist
            &mut *self.p.ptr.payload.get()
        }
    }
}
impl<'arena, T: Send + Sync> Drop for NetlistNodeWriteGuard<'arena, T> {
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

pub struct NetlistNodeReadGuard<'arena, T: Send + Sync> {
    pub p: NetlistNodeRef<'arena, T>,
    /// prevent this type from being `Sync`
    _pd: PhantomData<UnsafeCell<()>>,
}
impl<'arena, T: Send + Sync> Deref for NetlistNodeReadGuard<'arena, T> {
    type Target = T;

    fn deref<'guard>(&'guard self) -> &'guard T {
        unsafe {
            // safety: no way to get a &mut when read guards exist
            &*self.p.ptr.payload.get()
        }
    }
}
impl<'arena, T: Send + Sync> Drop for NetlistNodeReadGuard<'arena, T> {
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
    _wire: Option<NetlistWireRef<'arena>>,
}
pub type NetlistCellRef<'arena> = NetlistNodeRef<'arena, NetlistCell<'arena>>;
pub type NetlistCellWriteGuard<'arena> = NetlistNodeWriteGuard<'arena, NetlistCell<'arena>>;
pub type NetlistCellReadGuard<'arena> = NetlistNodeReadGuard<'arena, NetlistCell<'arena>>;
impl<'arena> NetlistCell<'arena> {
    pub unsafe fn init(self_: *mut Self) -> &'arena mut Self {
        (*self_)._wire = None;

        // safety: assert that we initialized everything
        &mut *self_
    }
}

/// Wires in a netlist
#[derive(Debug)]
pub struct NetlistWire<'arena> {
    // todo
    _cell: Option<NetlistCellRef<'arena>>,
}
pub type NetlistWireRef<'arena> = NetlistNodeRef<'arena, NetlistWire<'arena>>;
pub type NetlistWireWriteGuard<'arena> = NetlistNodeWriteGuard<'arena, NetlistWire<'arena>>;
pub type NetlistWireReadGuard<'arena> = NetlistNodeReadGuard<'arena, NetlistWire<'arena>>;
impl<'arena> NetlistWire<'arena> {
    pub unsafe fn init(self_: *mut Self) -> &'arena mut Self {
        (*self_)._cell = None;

        // safety: assert that we initialized everything
        &mut *self_
    }
}

#[derive(Debug)]
pub struct NetlistModule<'arena> {
    heap: SlabRoot<
        'arena,
        NetlistNodeWithLock<NetlistCell<'arena>>,
        NetlistNodeWithLock<NetlistWire<'arena>>,
    >,
}

impl<'arena> NetlistModule<'arena> {
    pub fn new() -> Self {
        Self {
            heap: SlabRoot::new(),
        }
    }
    pub fn new_thread(&'arena self) -> NetlistModuleThreadAccessor<'arena> {
        NetlistModuleThreadAccessor {
            heap_shard: self.heap.new_thread(),
        }
    }
}

#[derive(Debug)]
pub struct NetlistModuleThreadAccessor<'arena> {
    heap_shard: SlabThreadShard<
        'arena,
        NetlistNodeWithLock<NetlistCell<'arena>>,
        NetlistNodeWithLock<NetlistWire<'arena>>,
    >,
}

impl<'arena> NetlistModuleThreadAccessor<'arena> {
    pub fn new_cell<'wrapper>(&'wrapper self) -> NetlistCellWriteGuard<'arena> {
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
            NetlistCell::init((*new_obj_ptr).payload.get());

            NetlistCellWriteGuard {
                p: NetlistCellRef {
                    ptr: maybe_uninit.assume_init_ref(),
                    gen,
                },
                _pd: PhantomData,
            }
        }
    }

    pub fn new_wire<'wrapper>(&'wrapper self) -> NetlistWireWriteGuard<'arena> {
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
            NetlistWire::init((*new_obj_ptr).payload.get());

            NetlistWireWriteGuard {
                p: NetlistWireRef {
                    ptr: maybe_uninit.assume_init_ref(),
                    gen,
                },
                _pd: PhantomData,
            }
        }
    }

    pub fn delete_cell<'wrapper>(&'wrapper self, cell: NetlistCellWriteGuard<'arena>) {
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

    pub fn delete_wire<'wrapper>(&'wrapper self, wire: NetlistWireWriteGuard<'arena>) {
        // see notes above
        wire.p.ptr.lock_and_generation.store(0, Ordering::Relaxed);
        unsafe {
            // safety: just coercing between repr(C) union references
            self.heap_shard
                .free_netlist_wire(mem::transmute(wire.p.ptr))
        }
        mem::forget(wire);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn netlist_locking_smoke_test() {
        let netlist = NetlistModule::new();
        let thread = netlist.new_thread();

        let mut cell_0 = thread.new_cell();
        println!("Allocated new cell, {:?}", cell_0.p);

        let mut wire_0 = thread.new_wire();
        println!("Allocated new wire, {:?}", wire_0.p);

        cell_0._wire = Some(wire_0.p);
        wire_0._cell = Some(cell_0.p);

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
        let try_read = cell_0_p.try_read();
        assert!(try_read.is_ok());
        assert!(try_read.unwrap().is_none());
        let try_read = wire_0_p.try_read();
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

        let cell_0_r_0 = cell_0_p.try_read().unwrap().unwrap();
        let wire_0_r_0 = wire_0_p.try_read().unwrap().unwrap();

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

        assert_eq!(cell_0_r_0._wire, Some(wire_0_p));
        assert_eq!(wire_0_r_0._cell, Some(cell_0_p));

        let cell_0_r_1 = cell_0_p.try_read().unwrap().unwrap();
        let wire_0_r_1 = wire_0_p.try_read().unwrap().unwrap();

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

        assert_eq!(cell_0_r_1._wire, Some(wire_0_p));
        assert_eq!(wire_0_r_1._cell, Some(cell_0_p));

        let try_write = cell_0_p.try_write();
        assert!(try_write.is_ok());
        assert!(try_write.unwrap().is_none());
        let try_write = wire_0_p.try_write();
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

        let try_write = cell_0_p.try_write();
        assert!(try_write.is_ok());
        assert!(try_write.unwrap().is_none());
        let try_write = wire_0_p.try_write();
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

        let cell_0_re_w = cell_0_p.try_write().unwrap().unwrap();
        let wire_0_re_w = wire_0_p.try_write().unwrap().unwrap();

        println!("Re-reading cell again through write: {:?}", *cell_0_re_w);
        println!("Re-reading wire again through write: {:?}", *wire_0_re_w);

        assert_eq!(cell_0_re_w._wire, Some(wire_0_p));
        assert_eq!(wire_0_re_w._cell, Some(cell_0_p));

        thread.delete_cell(cell_0_re_w);

        // xxx reading "freed" memory!
        assert_eq!(cell_0_p.ptr.lock_and_generation.load(Ordering::SeqCst), 0);

        assert!(cell_0_p.try_write().is_err());
        assert!(cell_0_p.try_read().is_err());

        thread.delete_wire(wire_0_re_w);

        // xxx reading "freed" memory!
        assert_eq!(wire_0_p.ptr.lock_and_generation.load(Ordering::SeqCst), 0);

        assert!(wire_0_p.try_write().is_err());
        assert!(wire_0_p.try_read().is_err());
    }

    #[test]
    fn netlist_locking_smoke_test_generation() {
        let netlist = NetlistModule::new();
        let thread = netlist.new_thread();

        let cell_0 = thread.new_cell();
        let cell_0_p = cell_0.p;
        println!("Allocated new cell, {:?}", cell_0_p);
        thread.delete_cell(cell_0);

        let mut num_iters = 0;

        loop {
            let cell_i = thread.new_cell();
            let cell_i_p = cell_i.p;
            if cell_0_p.ptr as *const _ == cell_i_p.ptr {
                println!("Reused pointer detected after {} iters", num_iters);
                dbg!(cell_0_p);
                dbg!(cell_i_p);
                assert_ne!(cell_0_p.gen, cell_i_p.gen);

                assert!(cell_0_p.try_read().is_err());
                assert!(cell_0_p.try_write().is_err());

                break;
            }
            thread.delete_cell(cell_i);
            num_iters += 1;
        }
    }
}
