//! Locks built on top of [crate::stroad]
//!
//! Locks contain an AtomicU64 fast path, bit packed as follows:
//! - `bits[6:0]` = rwlock
//!     - 0 = not locked
//!     - !0 = write locked
//!     - else contains `n` readers
//! - `bits[7]` = might have threads parked
//! - `bits[62:8]` = generation counter
//! - `bits[63]` = valid (i.e. allocated)
//!
//! The `rwlock` field is only used for unordered algorithms and is
//! always 0 for ordered algorithms (as ordered algorithms always require
//! taking the hash bucket lock).
//!
//! NOTE: current impl restricts [MAX_THREADS] to never be more than 126
//!
//! XXX: The current implementation uses a super dangerous spicy trick.
//! This lock/generation field is stored at the very beginning of a heap
//! block, in a location that just so happens to overlap with
//! the heap free list next pointer once the block gets freed.
//! When a block is freed, the allocator will either store null or a valid
//! pointer in this location. Neither of these will have bit 63 set, so
//! we can detect if code tries to acquire a lock to a deleted object
//! (as long as the backing segment itself isn't deleted, which we won't do
//! while any graph algorithms are running).
//!
//! FIXME: How does this interact with MTE/PAC?
//!
//! NOTE: Generation counters are per-thread and not global. This is fine as it
//! is combined with the address itself in order to reference a specific node
//! (the address will come from different memory segments across different threads)

use std::cell::{Cell, UnsafeCell};
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::mem;
use std::ptr::addr_of_mut;
use std::sync::atomic::Ordering;

use tracing::Level;

use crate::allocator::*;
use crate::loom_testing::*;
use crate::stroad::*;
use crate::util::UsizePtr;

const _: () = assert!(MAX_THREADS <= 126);
/// Indicates that there is a valid object in this heap block (i.e. not a next pointer)
const LOCK_GEN_VALID_BIT: u64 = 1 << 63;
/// Indicates that there *might* be parked work items, only for unordered algorithms
const LOCK_GEN_MAYBE_PARKED_BIT: u64 = 1 << 7;
/// Extract the valid bit
pub const fn lock_gen_valid(x: u64) -> bool {
    x & LOCK_GEN_VALID_BIT != 0
}
/// Extract the generation counter
pub const fn lock_gen_gen(x: u64) -> u64 {
    (x >> 8) & 0x7FFFFFFFFFFFFF
}
/// Extract the "maybe has parked" bit
pub const fn lock_gen_maybe_parked(x: u64) -> bool {
    x & LOCK_GEN_MAYBE_PARKED_BIT != 0
}
/// Extracts the reader/writer count, only for unordered algorithms
pub const fn lock_gen_rwlock(x: u64) -> u8 {
    (x & 0x7F) as u8
}

/// Number of times to spin before asking stroad to park the current work item
#[cfg(not(loom))]
const SPIN_LIMIT: usize = 40;
#[cfg(loom)]
const SPIN_LIMIT: usize = 1;

/// Wrapped payload type, additionally containing a rwlock and generation counter
/// (for preventing ABA problem)
#[repr(C)]
#[derive(Debug)]
pub struct LockedObj<T> {
    /// R/W lock
    pub(crate) lock_and_generation: AtomicU64,
    /// Number of readers/writers, only when priority is used
    ///
    /// `bits[63]` = has a writer
    /// `bits[62:0]` = readers
    pub(crate) num_rw: UnsafeCell<u64>,
    /// Inner data
    pub(crate) payload: UnsafeCell<T>,
}
// safety: this is a wrapper for T where we manually enforce the
// shared xor mutable rules using atomics
unsafe impl<T: Send + Sync> Send for LockedObj<T> {}
unsafe impl<T: Send + Sync> Sync for LockedObj<T> {}
impl<T> LockedObj<T> {
    pub unsafe fn init(self_: *mut Self, gen: u64, xtra: u64) {
        (*self_)
            .lock_and_generation
            .store(LOCK_GEN_VALID_BIT | (gen << 8) | xtra, Ordering::Relaxed);
        *(*self_).num_rw.get() = 0;
    }
}

/// References to a node that has a lifetime from a particular heap
///
/// This is basically a fat pointer. It stores a raw pointer and an ABA generation counter.
/// They can be freely copied, sent between threads, etc.
///
/// These items compare with reference equality, not value equality.
pub struct ObjRef<'arena, T> {
    pub ptr: &'arena LockedObj<T>,
    pub gen: u64,
}
impl<'arena, T> ObjRef<'arena, T> {
    pub fn type_erase(self) -> TypeErasedObjRef<'arena> {
        TypeErasedObjRef {
            // safety: repr(C) and we don't actually access the payload
            ptr: unsafe { mem::transmute(self.ptr) },
            gen: self.gen,
        }
    }
}
// fixme justify why auto deriving doesn't work
impl<'arena, T> Clone for ObjRef<'arena, T> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            gen: self.gen,
        }
    }
}
impl<'arena, T> Copy for ObjRef<'arena, T> {}
impl<'arena, T> Debug for ObjRef<'arena, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(&format!("ObjRef<{}>", std::any::type_name::<T>()))
            .field("ptr", &(self.ptr as *const _))
            .field("gen", &self.gen)
            .finish()
    }
}
impl<'arena, T> PartialEq for ObjRef<'arena, T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr as *const _ == other.ptr as *const _ && self.gen == other.gen
    }
}
impl<'arena, T> Eq for ObjRef<'arena, T> {}
// fixme: do we need/want ord/partialord?
impl<'arena, T> Hash for ObjRef<'arena, T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (self.ptr as *const _ as usize).hash(state);
        self.gen.hash(state);
    }
}

/// [ObjRef], except ignoring what's in the payload (because the lock itself doesn't care)
pub type TypeErasedObjRef<'arena> = ObjRef<'arena, ()>;

/// States that a lock instance can be in
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LockState {
    Unlocked,
    Parked,
    LockedForUnorderedRead,
    LockedForUnorderedWrite,
    LockedForOrderedRead,
    LockedForOrderedWrite,
}
impl Default for LockState {
    fn default() -> Self {
        Self::Unlocked
    }
}

/// All the lock data (state enum and stroad module link pointers)
///
/// This object is intended to be not movable, using invariant lifetimes
/// and interior mutability. As soon as one of the lock methods is called,
/// the object becomes pinned.
///
/// This is *not* a RAII guard object, as the way we implement
/// that this object is immobile (self-lifetimes) prevents implementing [Drop]
pub struct LockAndStroadData<'arena, 'lock_inst, P> {
    /// State the lock is in
    pub(crate) state: Cell<LockState>,
    /// Object that this lock is protecting / potentially accessing
    pub(crate) p: TypeErasedObjRef<'arena>,
    /// Stroad module's state data
    // FIXME does this enforce too much invariance on lifetimes?
    stroad_state: UnsafeCell<StroadNode<'lock_inst, TypeErasedObjRef<'arena>, P>>,
    /// Prevent this type from being `Sync`, and
    /// ensure `'lock_inst` lifetime is invariant
    _pd1: PhantomData<UnsafeCell<&'lock_inst ()>>,
}

impl<'arena, 'lock_inst, P: Debug> Debug for LockAndStroadData<'arena, 'lock_inst, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("LockAndStroadData");
        dbg.field("state", &(self.state.get()));
        dbg.field("p", &self.p);
        dbg.field("stroad_state", unsafe { &*self.stroad_state.get() });
        dbg.finish()
    }
}
impl<'arena, 'lock_inst, P: StroadToWorkItemLink> LockAndStroadData<'arena, 'lock_inst, P> {
    /// Create a new lock state object
    pub fn new(obj: TypeErasedObjRef<'arena>, work_item_link: P) -> Self {
        Self {
            state: Cell::new(LockState::Unlocked),
            p: obj,
            stroad_state: UnsafeCell::new(StroadNode::new(work_item_link)),
            _pd1: PhantomData,
        }
    }

    /// Initialize a lock object in place, *EXCEPT* the external work item link
    pub unsafe fn init(self_: *mut Self, obj: TypeErasedObjRef<'arena>) {
        let tracing_span = tracing::span!(Level::TRACE, "LockAndStroadData::init");
        let _span_enter = tracing_span.enter();
        tracing::event!(
            name: "LockAndStroadData::init",
            Level::TRACE,
            lock_ptr = ?UsizePtr::from(self_),
            target.ptr = ?UsizePtr::from(obj.ptr),
            target.gen = obj.gen
        );

        (*self_).state = Cell::new(LockState::Unlocked);
        (*self_).p = obj;
        StroadNode::init((*self_).stroad_state.get());
    }

    /// Ugly get access to the work item link stored inside, so that it can be init-ed
    pub(crate) unsafe fn unsafe_stroad_work_item_link_ptr(self_: *const Self) -> *mut P {
        let stroad_state = (*self_).stroad_state.get();
        addr_of_mut!((*stroad_state).work_item_link)
    }

    /// Try to acquire an exclusive read/write lock, for an unordered algorithm
    ///
    /// Returns `Err(())` if the object has been deleted, or else `Ok(bool)`,
    /// where the bool indicates whether or not the locking was successful.
    pub fn unordered_try_write<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, TypeErasedObjRef<'arena>, P>,
    ) -> Result<bool, ()> {
        let tracing_span = tracing::span!(Level::TRACE, "LockAndStroadData::unordered_try_write", lock_ptr = ?UsizePtr::from(self), obj_ptr = ?self.p);
        let _span_enter = tracing_span.enter();
        tracing::event!(name: "lock_ops::lock", Level::TRACE, "lock");

        assert!(self.state.get() == LockState::Unlocked);
        let mut lock_inst = unsafe {
            // because
            // * this type isn't Sync
            // * this type is now pinned
            // * we have checked the state, such that this method can only be called
            //   when it is *not* part of the stroad's linked lists
            // this type coercion is acceptable
            let stroad_state = self.stroad_state.get();
            &mut *stroad_state
        };

        'batch_of_spins: loop {
            let mut spins = 0;
            let mut old_atomic_val = self.p.ptr.lock_and_generation.load(Ordering::Relaxed);
            'one_spin: loop {
                if spins == SPIN_LIMIT {
                    // try to set the "maybe has parked" bit, but spurious failures are ??? FIXME
                    let _ = self.p.ptr.lock_and_generation.compare_exchange_weak(
                        old_atomic_val,
                        old_atomic_val | LOCK_GEN_MAYBE_PARKED_BIT,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    );

                    // park us
                    match stroad.unordered_park_conditionally(lock_inst, self.p, || {
                        let lock_val = self.p.ptr.lock_and_generation.load(Ordering::Relaxed);
                        // park as long as object didn't get invalidated,
                        // and lock is still not available for us,
                        // and the "maybe has parked" bit is still set
                        if !lock_gen_valid(lock_val) {
                            // object invalidated (gone, deleted)
                            return false;
                        }
                        if lock_gen_gen(lock_val) != self.p.gen {
                            // object invalidated (gone, deleted)
                            return false;
                        }
                        if lock_gen_rwlock(lock_val) == 0 {
                            // lock available
                            return false;
                        }
                        if !lock_gen_maybe_parked(lock_val) {
                            // dropping other conflicting guards will clear this bit,
                            // so if it's clear we shouldn't park
                            return false;
                        }
                        true
                    }) {
                        Ok(_) => {
                            self.state.set(LockState::Parked);
                            return Ok(false);
                        }
                        Err(x) => lock_inst = x,
                    }

                    continue 'batch_of_spins;
                }

                if !lock_gen_valid(old_atomic_val) {
                    // object invalidated (gone, deleted)
                    return Err(());
                }
                if lock_gen_gen(old_atomic_val) != self.p.gen {
                    // object invalidated (gone, deleted)
                    return Err(());
                }
                if lock_gen_rwlock(old_atomic_val) != 0 {
                    // lock not available
                    if lock_gen_maybe_parked(old_atomic_val) {
                        spins = SPIN_LIMIT;
                    } else {
                        spins += 1;
                    }
                    old_atomic_val = self.p.ptr.lock_and_generation.load(Ordering::Relaxed);
                    spin_hint();
                    continue 'one_spin;
                }
                // lock available!
                let new_atomic_val = old_atomic_val | 0x7f;
                match self.p.ptr.lock_and_generation.compare_exchange_weak(
                    old_atomic_val,
                    new_atomic_val,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        // all good
                        self.state.set(LockState::LockedForUnorderedWrite);
                        return Ok(true);
                    }
                    Err(x) => {
                        // cas failed -> lock taken (or spurious)
                        spins += 1;
                        old_atomic_val = x;
                        spin_hint();
                        continue 'one_spin;
                    }
                }
            }
        }
    }

    /// Try to acquire a read-only lock, for an unordered algorithm
    ///
    /// Returns `Err(())` if the object has been deleted, or else `Ok(bool)`,
    /// where the bool indicates whether or not the locking was successful.
    pub fn unordered_try_read<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, TypeErasedObjRef<'arena>, P>,
    ) -> Result<bool, ()> {
        let tracing_span = tracing::span!(Level::TRACE, "LockAndStroadData::unordered_try_read", lock_ptr = ?UsizePtr::from(self), obj_ptr = ?self.p);
        let _span_enter = tracing_span.enter();
        tracing::event!(name: "lock_ops::lock", Level::TRACE, "lock");

        assert!(self.state.get() == LockState::Unlocked);
        let mut lock_inst = unsafe {
            // safety: see above
            let stroad_state = self.stroad_state.get();
            &mut *stroad_state
        };

        'batch_of_spins: loop {
            let mut spins = 0;
            let mut old_atomic_val = self.p.ptr.lock_and_generation.load(Ordering::Relaxed);
            'one_spin: loop {
                if spins == SPIN_LIMIT {
                    // try to set the "maybe has parked" bit, but spurious failures are ??? FIXME
                    let _ = self.p.ptr.lock_and_generation.compare_exchange_weak(
                        old_atomic_val,
                        old_atomic_val | LOCK_GEN_MAYBE_PARKED_BIT,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    );

                    // park us
                    match stroad.unordered_park_conditionally(lock_inst, self.p, || {
                        let lock_val = self.p.ptr.lock_and_generation.load(Ordering::Relaxed);
                        // park as long as object didn't get invalidated,
                        // and lock is still not available for us,
                        // and the "maybe has parked" bit is still set
                        if !lock_gen_valid(lock_val) {
                            // object invalidated (gone, deleted)
                            return false;
                        }
                        if lock_gen_gen(lock_val) != self.p.gen {
                            // object invalidated (gone, deleted)
                            return false;
                        }
                        if lock_gen_rwlock(lock_val) != 0x7f {
                            // lock available
                            return false;
                        }
                        if !lock_gen_maybe_parked(lock_val) {
                            // dropping other conflicting guards will clear this bit,
                            // so if it's clear we shouldn't park
                            return false;
                        }
                        true
                    }) {
                        Ok(_) => {
                            self.state.set(LockState::Parked);
                            return Ok(false);
                        }
                        Err(x) => lock_inst = x,
                    }

                    continue 'batch_of_spins;
                }

                if !lock_gen_valid(old_atomic_val) {
                    // object invalidated (gone, deleted)
                    return Err(());
                }
                if lock_gen_gen(old_atomic_val) != self.p.gen {
                    // object invalidated (gone, deleted)
                    return Err(());
                }
                if lock_gen_rwlock(old_atomic_val) == 0x7f {
                    // lock not available
                    if lock_gen_maybe_parked(old_atomic_val) {
                        spins = SPIN_LIMIT;
                    } else {
                        spins += 1;
                    }
                    old_atomic_val = self.p.ptr.lock_and_generation.load(Ordering::Relaxed);
                    spin_hint();
                    continue 'one_spin;
                }
                // lock available!
                let new_atomic_val = old_atomic_val + 1;
                match self.p.ptr.lock_and_generation.compare_exchange_weak(
                    old_atomic_val,
                    new_atomic_val,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        // all good
                        self.state.set(LockState::LockedForUnorderedRead);
                        return Ok(true);
                    }
                    Err(x) => {
                        // cas failed -> lock taken (or spurious)
                        spins += 1;
                        old_atomic_val = x;
                        spin_hint();
                        continue 'one_spin;
                    }
                }
            }
        }
    }

    /// Try to acquire a read/write lock, for an ordered algorithm.
    ///
    /// This can return success even if there are other readers, as long as
    /// the readers have strictly higher priority than this item.
    ///
    /// Actually writing (without data races) is only allowed if the work item
    /// is at the head of the commit queue, which this module doesn't check!
    ///
    /// Returns `Err(())` if the object has been deleted, or else `Ok(bool)`,
    /// where the bool indicates whether or not the locking was successful.
    pub fn ordered_try_write<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, TypeErasedObjRef<'arena>, P>,
        prio: u64,
    ) -> Result<bool, ()> {
        let tracing_span = tracing::span!(Level::TRACE, "LockAndStroadData::ordered_try_write", lock_ptr = ?UsizePtr::from(self), obj_ptr = ?self.p);
        let _span_enter = tracing_span.enter();
        tracing::event!(name: "lock_ops::lock", Level::TRACE, "lock");

        assert!(self.state.get() == LockState::Unlocked);
        let lock_inst = unsafe {
            // safety: see above
            let stroad_state = self.stroad_state.get();
            &mut *stroad_state
        };

        debug_assert!(prio < i64::MAX as u64);
        let prio = -(prio as i64) - 1;

        let old_atomic_val = self.p.ptr.lock_and_generation.load(Ordering::Relaxed);
        if !lock_gen_valid(old_atomic_val) {
            // object invalidated (gone, deleted)
            return Err(());
        }
        if lock_gen_gen(old_atomic_val) != self.p.gen {
            // object invalidated (gone, deleted)
            return Err(());
        }
        // xxx the above checks are sufficient because deallocating can only be done
        // through a write guard, during the commit phase
        // xxx is this right?

        // object exists, try to lock it
        let (locked, _) = stroad.ordered_do_locking(lock_inst, self.p, prio, || {
            // here the bucket lock is held, so we indirectly have exclusive access to the
            // object we are trying to lock, which means that we can manipulate this counter
            let num_rw = self.p.ptr.num_rw.get();
            unsafe {
                *num_rw |= 0x8000000000000000;
            }
        });

        if locked {
            self.state.set(LockState::LockedForOrderedWrite);
            Ok(true)
        } else {
            self.state.set(LockState::Parked);
            Ok(false)
        }
    }

    /// Try to acquire a read-only lock, for an ordered algorithm.
    ///
    /// This can return success even if there is a writer, as long as
    /// the writer has strictly lower priority than this item.
    ///
    /// Returns `Err(())` if the object has been deleted, or else `Ok(bool)`,
    /// where the bool indicates whether or not the locking was successful.
    pub fn ordered_try_read<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, TypeErasedObjRef<'arena>, P>,
        prio: u64,
    ) -> Result<bool, ()> {
        let tracing_span = tracing::span!(Level::TRACE, "LockAndStroadData::ordered_try_read", lock_ptr = ?UsizePtr::from(self), obj_ptr = ?self.p);
        let _span_enter = tracing_span.enter();
        tracing::event!(name: "lock_ops::lock", Level::TRACE, "lock");

        assert!(self.state.get() == LockState::Unlocked);
        let lock_inst = unsafe {
            // safety: see above
            let stroad_state = self.stroad_state.get();
            &mut *stroad_state
        };

        debug_assert!(prio < i64::MAX as u64);
        let prio = prio as i64;

        let old_atomic_val = self.p.ptr.lock_and_generation.load(Ordering::Relaxed);
        if !lock_gen_valid(old_atomic_val) {
            // object invalidated (gone, deleted)
            return Err(());
        }
        if lock_gen_gen(old_atomic_val) != self.p.gen {
            // object invalidated (gone, deleted)
            return Err(());
        }
        // xxx the above checks are sufficient because deallocating can only be done
        // through a write guard, during the commit phase
        // xxx is this right?

        // object exists, try to lock it
        let (locked, _) = stroad.ordered_do_locking(lock_inst, self.p, prio, || {
            // here the bucket lock is held, so we indirectly have exclusive access to the
            // object we are trying to lock, which means that we can manipulate this counter
            let num_rw = self.p.ptr.num_rw.get();
            unsafe {
                let old_num_rw = *num_rw;
                *num_rw =
                    ((old_num_rw & 0x7fffffffffffffff) + 1) | (old_num_rw & 0x8000000000000000);
            }
        });

        if locked {
            self.state.set(LockState::LockedForOrderedRead);
            Ok(true)
        } else {
            self.state.set(LockState::Parked);
            Ok(false)
        }
    }

    /// Unlocks the object that this lock protects.
    ///
    /// Automatically dispatches based on the stored state,
    /// and also unparks other work items only as appropriate.
    ///
    /// This method is unsafe for the following reasons:
    /// * you need to pass in *the same* stroad object used to lock it.
    ///   (not storing this saves memory)
    /// * you can only call this when no references to the protected data exist
    pub unsafe fn unlock<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, TypeErasedObjRef<'arena>, P>,
        unpark_xtra: &mut P::UnparkXtraTy,
    ) {
        match self.state.get() {
            LockState::Unlocked => {
                // don't have to do anything, haven't even tried locking
            }
            LockState::Parked => {
                // fixme: what are we supposed to do here?
            }
            LockState::LockedForUnorderedRead => self.unlock_unordered_read(stroad, unpark_xtra),
            LockState::LockedForUnorderedWrite => self.unlock_unordered_write(stroad, unpark_xtra),
            LockState::LockedForOrderedRead => self.unlock_ordered_read(stroad, unpark_xtra),
            LockState::LockedForOrderedWrite => self.unlock_ordered_write(stroad, unpark_xtra),
        }
    }

    /// Unlock for an unordered r/w lock
    ///
    /// Always unparks everything
    fn unlock_unordered_write<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, TypeErasedObjRef<'arena>, P>,
        unpark_xtra: &mut P::UnparkXtraTy,
    ) {
        let tracing_span = tracing::span!(Level::TRACE, "LockAndStroadData::unlock_unordered_write", lock_ptr = ?UsizePtr::from(self), obj_ptr = ?self.p);
        let _span_enter = tracing_span.enter();
        tracing::event!(name: "lock_ops::unlock", Level::TRACE, "unlock");

        // we have exclusive access
        // we need to push out all previous memory accesses
        // and establish synchronizes-with trying to get access
        let old_atomic_val = self
            .p
            .ptr
            .lock_and_generation
            .fetch_and(!0xff, Ordering::Release);
        // note that we cleared *both* the rwlock and "maybe has parked" bits

        debug_assert!(lock_gen_valid(old_atomic_val));
        debug_assert_eq!(lock_gen_gen(old_atomic_val), self.p.gen);
        debug_assert_eq!(lock_gen_rwlock(old_atomic_val), 0x7f);

        if lock_gen_maybe_parked(old_atomic_val) {
            stroad.unordered_unpark_all(&self.p, unpark_xtra);
        }

        self.state.set(LockState::Unlocked);
    }

    /// Unlock for an unordered r/o lock
    ///
    /// Unparks if we are the final reader
    fn unlock_unordered_read<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, TypeErasedObjRef<'arena>, P>,
        unpark_xtra: &mut P::UnparkXtraTy,
    ) {
        let tracing_span = tracing::span!(Level::TRACE, "LockAndStroadData::unlock_unordered_read", lock_ptr = ?UsizePtr::from(self), obj_ptr = ?self.p);
        let _span_enter = tracing_span.enter();
        tracing::event!(name: "lock_ops::unlock", Level::TRACE, "unlock");

        let mut old_atomic_val = self.p.ptr.lock_and_generation.load(Ordering::Relaxed);
        loop {
            debug_assert!(lock_gen_valid(old_atomic_val));
            debug_assert_eq!(lock_gen_gen(old_atomic_val), self.p.gen);
            debug_assert_ne!(lock_gen_rwlock(old_atomic_val), 0x7f);
            debug_assert_ne!(lock_gen_rwlock(old_atomic_val), 0);
            let mut new_atomic_val = old_atomic_val - 1;
            if lock_gen_rwlock(old_atomic_val) == 1 {
                new_atomic_val &= !LOCK_GEN_MAYBE_PARKED_BIT;
            }
            // ordering: in order to prevent reads to data from moving
            // after this atomic update, we *still* need release ordering
            // (even though no data is modified)
            match self.p.ptr.lock_and_generation.compare_exchange_weak(
                old_atomic_val,
                new_atomic_val,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    if lock_gen_rwlock(old_atomic_val) == 1 && lock_gen_maybe_parked(old_atomic_val)
                    {
                        // fixme can we optimize this?
                        stroad.unordered_unpark_all(&self.p, unpark_xtra);
                    }
                    break;
                }
                Err(x) => old_atomic_val = x,
            }
        }

        self.state.set(LockState::Unlocked);
    }

    /// Unlock for an ordered r/w lock
    ///
    /// Always unparks everything
    fn unlock_ordered_write<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, TypeErasedObjRef<'arena>, P>,
        unpark_xtra: &mut P::UnparkXtraTy,
    ) {
        let tracing_span = tracing::span!(Level::TRACE, "LockAndStroadData::unlock_ordered_write", lock_ptr = ?UsizePtr::from(self), obj_ptr = ?self.p);
        let _span_enter = tracing_span.enter();
        tracing::event!(name: "lock_ops::unlock", Level::TRACE, "unlock");

        let lock_inst = unsafe {
            // safety: this can only be called when we hold the lock
            // so we know there's no &mut out there
            let stroad_state = self.stroad_state.get();
            &*stroad_state
        };
        stroad.ordered_do_unlocking(
            lock_inst,
            || true,
            || {
                // here we clearing this flag
                // and bucket lock is still held
                let num_rw = self.p.ptr.num_rw.get();
                unsafe {
                    *num_rw &= !0x8000000000000000;
                }
            },
            unpark_xtra,
        );

        self.state.set(LockState::Unlocked);
    }

    /// Unlock for an ordered r/o lock
    ///
    /// Unparks if we are the final reader *and* there isn't a writer
    fn unlock_ordered_read<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, TypeErasedObjRef<'arena>, P>,
        unpark_xtra: &mut P::UnparkXtraTy,
    ) {
        let tracing_span = tracing::span!(Level::TRACE, "LockAndStroadData::unlock_ordered_read", lock_ptr = ?UsizePtr::from(self), obj_ptr = ?self.p);
        let _span_enter = tracing_span.enter();
        tracing::event!(name: "lock_ops::unlock", Level::TRACE, "unlock");

        let lock_inst = unsafe {
            // safety: this can only be called when we hold the lock
            // so we know there's no &mut out there
            let stroad_state = self.stroad_state.get();
            &*stroad_state
        };
        stroad.ordered_do_unlocking(
            lock_inst,
            || {
                let num_rw = self.p.ptr.num_rw.get();
                // check if we are the last reader, and that there is no writer
                unsafe { *num_rw == 1 }
            },
            || {
                let num_rw = self.p.ptr.num_rw.get();
                unsafe {
                    let old_num_rw = *num_rw;
                    *num_rw =
                        ((old_num_rw & 0x7fffffffffffffff) - 1) | (old_num_rw & 0x8000000000000000);
                }
            },
            unpark_xtra,
        );
    }
}

#[cfg(test)]
mod tests;
