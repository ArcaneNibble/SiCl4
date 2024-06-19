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
use std::sync::atomic::Ordering;

use crate::allocator::*;
use crate::loom_testing::*;
use crate::stroad::*;

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
    num_rw: UnsafeCell<u64>,
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

/// States that a lock instance can be in
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LockState {
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

/// Lock state object
///
/// This object is intended to be not movable, using invariant lifetimes
/// and interior mutability. As soon as one of the lock methods is called,
/// the object becomes pinned.
///
/// This is *not* a RAII guard object, as the way we implement
/// that this object is immobile (self-lifetimes) prevents implementing [Drop]
pub struct RWLock<'arena, 'lock_inst, T, P> {
    /// State the lock is in
    state: Cell<LockState>,
    /// Object that this lock is protecting / potentially accessing
    pub p: ObjRef<'arena, T>,
    /// Stroad module's state data
    // FIXME does this enforce too much invariance on lifetimes?
    stroad_state: UnsafeCell<LockInstance<'lock_inst, ObjRef<'arena, T>, P>>,
    /// Prevent this type from being `Sync`, and
    /// ensure `'lock_inst` lifetime is invariant
    _pd1: PhantomData<UnsafeCell<&'lock_inst ()>>,
}

impl<'arena, 'lock_inst, T, P: Debug> Debug for RWLock<'arena, 'lock_inst, T, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("RWLock");
        dbg.field("state", &(self.state.get()));
        dbg.field("p", &self.p);
        dbg.field("stroad_state", unsafe { &*self.stroad_state.get() });
        dbg.finish()
    }
}
impl<'arena, 'lock_inst, T, P: LockInstPayload> RWLock<'arena, 'lock_inst, T, P> {
    /// Create a new lock state object
    pub fn new(obj: ObjRef<'arena, T>, payload: P) -> Self {
        Self {
            state: Cell::new(LockState::Unlocked),
            p: obj,
            stroad_state: UnsafeCell::new(LockInstance::new(payload)),
            _pd1: PhantomData,
        }
    }

    /// Initialize a lock object in place, *EXCEPT* the external payload
    pub unsafe fn init(self_: *mut Self, obj: ObjRef<'arena, T>) {
        (*self_).state = Cell::new(LockState::Unlocked);
        (*self_).p = obj;
        LockInstance::init((*self_).stroad_state.get());
    }

    /// Try to acquire an exclusive read/write lock, for an unordered algorithm
    ///
    /// Returns `Err(())` if the object has been deleted, or else `Ok(bool)`,
    /// where the bool indicates whether or not the locking was successful.
    pub fn unordered_try_write<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, ObjRef<'arena, T>, P>,
    ) -> Result<bool, ()> {
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
        stroad: &'stroad Stroad<'lock_inst, ObjRef<'arena, T>, P>,
    ) -> Result<bool, ()> {
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
        stroad: &'stroad Stroad<'lock_inst, ObjRef<'arena, T>, P>,
        prio: u64,
    ) -> Result<bool, ()> {
        assert!(self.state.get() == LockState::Unlocked);
        let lock_inst = unsafe {
            // safety: see above
            let stroad_state = self.stroad_state.get();
            &mut *stroad_state
        };

        debug_assert!(prio <= i64::MAX as u64);
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
        stroad: &'stroad Stroad<'lock_inst, ObjRef<'arena, T>, P>,
        prio: u64,
    ) -> Result<bool, ()> {
        assert!(self.state.get() == LockState::Unlocked);
        let lock_inst = unsafe {
            // safety: see above
            let stroad_state = self.stroad_state.get();
            &mut *stroad_state
        };

        debug_assert!(prio <= i64::MAX as u64);
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
        stroad: &'stroad Stroad<'lock_inst, ObjRef<'arena, T>, P>,
    ) {
        match self.state.get() {
            LockState::Unlocked => {
                // don't have to do anything, haven't even tried locking
            }
            LockState::Parked => {
                // fixme: what are we supposed to do here?
            }
            LockState::LockedForUnorderedRead => self.unlock_unordered_read(stroad),
            LockState::LockedForUnorderedWrite => self.unlock_unordered_write(stroad),
            LockState::LockedForOrderedRead => self.unlock_ordered_read(stroad),
            LockState::LockedForOrderedWrite => self.unlock_ordered_write(stroad),
        }
    }

    /// Unlock for an unordered r/w lock
    ///
    /// Always unparks everything
    fn unlock_unordered_write<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, ObjRef<'arena, T>, P>,
    ) {
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
            stroad.unordered_unpark_all(&self.p);
        }

        self.state.set(LockState::Unlocked);
    }

    /// Unlock for an unordered r/o lock
    ///
    /// Unparks if we are the final reader
    fn unlock_unordered_read<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, ObjRef<'arena, T>, P>,
    ) {
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
                        stroad.unordered_unpark_all(&self.p);
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
        stroad: &'stroad Stroad<'lock_inst, ObjRef<'arena, T>, P>,
    ) {
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
        );

        self.state.set(LockState::Unlocked);
    }

    /// Unlock for an ordered r/o lock
    ///
    /// Unparks if we are the final reader *and* there isn't a writer
    fn unlock_ordered_read<'stroad>(
        &'lock_inst self,
        stroad: &'stroad Stroad<'lock_inst, ObjRef<'arena, T>, P>,
    ) {
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
        );
    }
}

#[cfg(test)]
mod tests {
    use std::alloc::Layout;

    use super::*;

    #[derive(Default, Debug)]
    struct LockingTestingPayload {
        unparked: bool,
        cancelled: bool,
    }
    impl LockInstPayload for LockingTestingPayload {
        fn unpark<'lock_inst, K>(e: &'lock_inst mut LockInstance<'lock_inst, K, Self>)
        where
            Self: Sized,
        {
            e.payload.unparked = true;
        }

        fn cancel<'lock_inst, K>(e: &'lock_inst mut LockInstance<'lock_inst, K, Self>)
        where
            Self: Sized,
        {
            e.payload.cancelled = true;
        }
    }

    struct JustU32Mapper {}
    impl TypeMapper for JustU32Mapper {
        type BinsArrayTy<T> = [T; 1];
        const LAYOUTS: &'static [&'static [Layout]] = &[&[Layout::new::<LockedObj<u32>>()]];
    }
    impl TypeMappable<JustU32Mapper> for LockedObj<u32> {
        const I: usize = 0;
    }
    type ObjRefLockedU32<'arena> = ObjRef<'arena, u32>;

    #[test]
    #[ignore = "not automated, human eye verified"]
    fn locking_manual_tests() {
        let alloc = SlabRoot::<JustU32Mapper>::new();
        let thread_shard = alloc.new_thread();
        let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
        let obj = unsafe {
            let obj_p = obj.as_mut_ptr();
            (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
            (*obj_p).num_rw = UnsafeCell::new(0);
            (*obj_p).payload = UnsafeCell::new(12345);
            obj.assume_init_ref()
        };
        dbg!(&obj);
        let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
        dbg!(&obj_ref);

        let stroad = Stroad::<ObjRefLockedU32, LockingTestingPayload>::new();

        #[allow(unused_mut)]
        let mut lock = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        dbg!(&lock);
        let ret = lock.unordered_try_write(&stroad);
        dbg!(&ret);
        let _ = ret.is_ok();
        dbg!(&lock);

        unsafe {
            lock.unlock(&stroad);
        }
        dbg!(&lock);

        // can't work
        // let mut _lock2 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
        //     obj_ref,
        //     LockingTestingPayload::default(),
        // );
        // std::mem::swap(&mut lock, &mut _lock2);
    }

    #[cfg(loom)]
    #[test]
    fn locking_loom_unordered_ww_nounlock() {
        loom::model(|| {
            let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustU32Mapper>::new()));
            let thread_shard = alloc.new_thread();
            let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
            let obj = unsafe {
                let obj_p = obj.as_mut_ptr();
                (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
                (*obj_p).num_rw = UnsafeCell::new(0);
                (*obj_p).payload = UnsafeCell::new(12345);
                obj.assume_init_ref()
            };
            let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
            drop(thread_shard);
            let stroad = &*Box::leak(Stroad::<ObjRefLockedU32, LockingTestingPayload>::new());

            let t1_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));
            let t2_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));

            let t1 = loom::thread::spawn(move || {
                let lock = &*Box::leak(Box::new(RWLock::new(
                    obj_ref,
                    LockingTestingPayload::default(),
                )));
                let ret = lock.unordered_try_write(stroad);

                assert!(ret.is_ok());
                t1_got_lock.store(ret.unwrap(), Ordering::Relaxed);
            });
            let t2 = loom::thread::spawn(move || {
                let lock = &*Box::leak(Box::new(RWLock::new(
                    obj_ref,
                    LockingTestingPayload::default(),
                )));
                let ret = lock.unordered_try_write(stroad);

                assert!(ret.is_ok());
                t2_got_lock.store(ret.unwrap(), Ordering::Relaxed);
            });

            t1.join().unwrap();
            t2.join().unwrap();

            let t1_got_lock = t1_got_lock.load(Ordering::Relaxed);
            let t2_got_lock = t2_got_lock.load(Ordering::Relaxed);

            // one of the two *must* succeed
            assert!(t1_got_lock != t2_got_lock);
        });
    }

    #[cfg(loom)]
    #[test]
    fn locking_loom_unordered_rw_nounlock() {
        loom::model(|| {
            let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustU32Mapper>::new()));
            let thread_shard = alloc.new_thread();
            let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
            let obj = unsafe {
                let obj_p = obj.as_mut_ptr();
                (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
                (*obj_p).num_rw = UnsafeCell::new(0);
                (*obj_p).payload = UnsafeCell::new(12345);
                obj.assume_init_ref()
            };
            let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
            drop(thread_shard);
            let stroad = &*Box::leak(Stroad::<ObjRefLockedU32, LockingTestingPayload>::new());

            let t1_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));
            let t2_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));

            let t1 = loom::thread::spawn(move || {
                let lock = &*Box::leak(Box::new(RWLock::new(
                    obj_ref,
                    LockingTestingPayload::default(),
                )));
                let ret = lock.unordered_try_read(stroad);

                assert!(ret.is_ok());
                t1_got_lock.store(ret.unwrap(), Ordering::Relaxed);
            });
            let t2 = loom::thread::spawn(move || {
                let lock = &*Box::leak(Box::new(RWLock::new(
                    obj_ref,
                    LockingTestingPayload::default(),
                )));
                let ret = lock.unordered_try_write(stroad);

                assert!(ret.is_ok());
                t2_got_lock.store(ret.unwrap(), Ordering::Relaxed);
            });

            t1.join().unwrap();
            t2.join().unwrap();

            let t1_got_lock = t1_got_lock.load(Ordering::Relaxed);
            let t2_got_lock = t2_got_lock.load(Ordering::Relaxed);

            // one of the two *must* succeed
            assert!(t1_got_lock != t2_got_lock);
        });
    }

    #[cfg(loom)]
    #[test]
    fn locking_loom_unordered_rr_nounlock() {
        loom::model(|| {
            let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustU32Mapper>::new()));
            let thread_shard = alloc.new_thread();
            let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
            let obj = unsafe {
                let obj_p = obj.as_mut_ptr();
                (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
                (*obj_p).num_rw = UnsafeCell::new(0);
                (*obj_p).payload = UnsafeCell::new(12345);
                obj.assume_init_ref()
            };
            let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
            drop(thread_shard);
            let stroad = &*Box::leak(Stroad::<ObjRefLockedU32, LockingTestingPayload>::new());

            let t1_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));
            let t2_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));

            let t1 = loom::thread::spawn(move || {
                let lock = &*Box::leak(Box::new(RWLock::new(
                    obj_ref,
                    LockingTestingPayload::default(),
                )));
                let ret = lock.unordered_try_read(stroad);

                assert!(ret.is_ok());
                t1_got_lock.store(ret.unwrap(), Ordering::Relaxed);
            });
            let t2 = loom::thread::spawn(move || {
                let lock = &*Box::leak(Box::new(RWLock::new(
                    obj_ref,
                    LockingTestingPayload::default(),
                )));
                let ret = lock.unordered_try_read(stroad);

                assert!(ret.is_ok());
                t2_got_lock.store(ret.unwrap(), Ordering::Relaxed);
            });

            t1.join().unwrap();
            t2.join().unwrap();

            let t1_got_lock = t1_got_lock.load(Ordering::Relaxed);
            let t2_got_lock = t2_got_lock.load(Ordering::Relaxed);

            // *both* must succeed
            assert!(t1_got_lock && t2_got_lock);
        });
    }

    #[cfg(loom)]
    #[test]
    fn locking_loom_unordered_ww_unlock() {
        loom::model(|| {
            let alloc = &*Box::leak(Box::new(SlabRoot::<'static, JustU32Mapper>::new()));
            let thread_shard = alloc.new_thread();
            let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
            let obj = unsafe {
                let obj_p = obj.as_mut_ptr();
                (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
                (*obj_p).num_rw = UnsafeCell::new(0);
                (*obj_p).payload = UnsafeCell::new(12345);
                obj.assume_init_ref()
            };
            let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
            drop(thread_shard);
            let stroad = &*Box::leak(Stroad::<ObjRefLockedU32, LockingTestingPayload>::new());

            let t1_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));
            let t2_got_lock = &*Box::leak(Box::new(AtomicBool::new(false)));

            let t1_lock = &*Box::leak(Box::new(RWLock::new(
                obj_ref,
                LockingTestingPayload::default(),
            )));
            let t2_lock = &*Box::leak(Box::new(RWLock::new(
                obj_ref,
                LockingTestingPayload::default(),
            )));

            // println!("~~~~~ MODEL ITER ~~~~~");

            let t1 = loom::thread::spawn(move || {
                let ret = t1_lock.unordered_try_write(stroad);

                assert!(ret.is_ok());
                if ret.unwrap() {
                    t1_got_lock.store(true, Ordering::Relaxed);
                    // needed in order to simulate processing taking some time
                    loom::thread::yield_now();
                    unsafe {
                        t1_lock.unlock(stroad);
                    }
                }
            });
            let t2 = loom::thread::spawn(move || {
                let ret = t2_lock.unordered_try_write(stroad);

                assert!(ret.is_ok());
                if ret.unwrap() {
                    t2_got_lock.store(true, Ordering::Relaxed);
                    // needed in order to simulate processing taking some time
                    loom::thread::yield_now();
                    // drop guard
                    unsafe {
                        t2_lock.unlock(stroad);
                    }
                }
            });

            t1.join().unwrap();
            t2.join().unwrap();

            let t1_got_lock = t1_got_lock.load(Ordering::Relaxed);
            let t2_got_lock = t2_got_lock.load(Ordering::Relaxed);
            // xxx
            unsafe {
                match (t1_got_lock, t2_got_lock) {
                    (true, true) => {
                        assert!(!(*t1_lock.stroad_state.get()).payload.unparked);
                        assert!(!(*t1_lock.stroad_state.get()).payload.cancelled);
                        assert!(!(*t2_lock.stroad_state.get()).payload.unparked);
                        assert!(!(*t2_lock.stroad_state.get()).payload.cancelled);
                    }
                    (true, false) => {
                        assert!(!(*t1_lock.stroad_state.get()).payload.unparked);
                        assert!(!(*t1_lock.stroad_state.get()).payload.cancelled);
                        assert!((*t2_lock.stroad_state.get()).payload.unparked);
                        assert!(!(*t2_lock.stroad_state.get()).payload.cancelled);
                    }
                    (false, true) => {
                        assert!((*t1_lock.stroad_state.get()).payload.unparked);
                        assert!(!(*t1_lock.stroad_state.get()).payload.cancelled);
                        assert!(!(*t2_lock.stroad_state.get()).payload.unparked);
                        assert!(!(*t2_lock.stroad_state.get()).payload.cancelled);
                    }
                    (false, false) => {
                        panic!("both locks failed to grab")
                    }
                }
            }
        });
    }
    // fixme: the cas loop makes thw _rw_unlock and _rr_unlock tests too slow

    #[cfg(not(loom))]
    #[test]
    fn locking_single_threaded_write_unpark_sim() {
        let alloc = SlabRoot::<JustU32Mapper>::new();
        let thread_shard = alloc.new_thread();
        let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
        let obj = unsafe {
            let obj_p = obj.as_mut_ptr();
            (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
            (*obj_p).num_rw = UnsafeCell::new(0);
            (*obj_p).payload = UnsafeCell::new(12345);
            obj.assume_init_ref()
        };
        let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
        drop(thread_shard);

        let stroad = Stroad::<ObjRefLockedU32, LockingTestingPayload>::new();

        let lock_0 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_0.unordered_try_write(&stroad);
        assert_eq!(ret, Ok(true));
        assert_eq!(
            obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
            0x800000000000007f | (gen << 8)
        );

        let lock_1 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_1.unordered_try_write(&stroad);
        assert_eq!(ret, Ok(false));
        assert_eq!(
            obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
            0x80000000000000ff | (gen << 8)
        );

        unsafe {
            lock_0.unlock(&stroad);
            assert_eq!(
                obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
                0x8000000000000000 | (gen << 8)
            );
            assert!((*lock_1.stroad_state.get()).payload.unparked);
        }
    }

    #[cfg(not(loom))]
    #[test]
    fn locking_single_threaded_read_unpark_sim() {
        let alloc = SlabRoot::<JustU32Mapper>::new();
        let thread_shard = alloc.new_thread();
        let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
        let obj = unsafe {
            let obj_p = obj.as_mut_ptr();
            (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
            (*obj_p).num_rw = UnsafeCell::new(0);
            (*obj_p).payload = UnsafeCell::new(12345);
            obj.assume_init_ref()
        };
        let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
        drop(thread_shard);

        let stroad = Stroad::<ObjRefLockedU32, LockingTestingPayload>::new();

        let lock_0 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_0.unordered_try_read(&stroad);
        assert_eq!(ret, Ok(true));
        assert_eq!(
            obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
            0x8000000000000001 | (gen << 8)
        );

        let lock_1 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_1.unordered_try_read(&stroad);
        assert_eq!(ret, Ok(true));
        assert_eq!(
            obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
            0x8000000000000002 | (gen << 8)
        );

        let lock_2 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_2.unordered_try_write(&stroad);
        assert_eq!(ret, Ok(false));
        assert_eq!(
            obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
            0x8000000000000082 | (gen << 8)
        );

        unsafe {
            lock_0.unlock(&stroad);
            assert!(!(*lock_2.stroad_state.get()).payload.unparked);
            assert_eq!(
                obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
                0x8000000000000081 | (gen << 8)
            );
            lock_1.unlock(&stroad);
            assert!((*lock_2.stroad_state.get()).payload.unparked);
            assert_eq!(
                obj_ref.ptr.lock_and_generation.load(Ordering::Relaxed),
                0x8000000000000000 | (gen << 8)
            );
        }
    }

    #[cfg(not(loom))]
    #[test]
    fn locking_single_threaded_ordered_write_causes_unpark_sim() {
        let alloc = SlabRoot::<JustU32Mapper>::new();
        let thread_shard = alloc.new_thread();
        let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
        let obj = unsafe {
            let obj_p = obj.as_mut_ptr();
            (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
            (*obj_p).num_rw = UnsafeCell::new(0);
            (*obj_p).payload = UnsafeCell::new(12345);
            obj.assume_init_ref()
        };
        let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
        drop(thread_shard);

        let stroad = Stroad::<ObjRefLockedU32, LockingTestingPayload>::new();

        let lock_0 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_0.ordered_try_read(&stroad, 0);
        assert_eq!(ret, Ok(true));
        assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 1);

        let lock_1 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_1.ordered_try_write(&stroad, 1);
        assert_eq!(ret, Ok(true));
        assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

        let lock_2 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_2.ordered_try_read(&stroad, 2);
        assert_eq!(ret, Ok(false));
        assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

        unsafe {
            // the read shouldn't trigger an unpark
            lock_0.unlock(&stroad);
            assert!(!(*lock_2.stroad_state.get()).payload.unparked);
            assert_eq!(*obj_ref.ptr.num_rw.get(), 0x8000000000000000);
            // but the write should
            lock_1.unlock(&stroad);
            assert!((*lock_2.stroad_state.get()).payload.unparked);
            assert_eq!(*obj_ref.ptr.num_rw.get(), 0);
        }
    }

    #[cfg(not(loom))]
    #[test]
    fn locking_single_threaded_ordered_read_causes_unpark_sim() {
        let alloc = SlabRoot::<JustU32Mapper>::new();
        let thread_shard = alloc.new_thread();
        let (obj, gen) = thread_shard.allocate::<LockedObj<u32>>();
        let obj = unsafe {
            let obj_p = obj.as_mut_ptr();
            (*obj_p).lock_and_generation = AtomicU64::new(LOCK_GEN_VALID_BIT | (gen << 8));
            (*obj_p).num_rw = UnsafeCell::new(0);
            (*obj_p).payload = UnsafeCell::new(12345);
            obj.assume_init_ref()
        };
        let obj_ref = ObjRefLockedU32 { ptr: obj, gen };
        drop(thread_shard);

        let stroad = Stroad::<ObjRefLockedU32, LockingTestingPayload>::new();

        let lock_0 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_0.ordered_try_read(&stroad, 0);
        assert_eq!(ret, Ok(true));
        assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 1);

        let lock_1 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_1.ordered_try_write(&stroad, 1);
        assert_eq!(ret, Ok(true));
        assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

        let lock_2 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_2.ordered_try_read(&stroad, 2);
        assert_eq!(ret, Ok(false));
        assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

        let lock_3 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_3.ordered_try_read(&stroad, 3);
        assert_eq!(ret, Ok(false));
        assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

        let lock_4 = RWLock::<'_, '_, u32, LockingTestingPayload>::new(
            obj_ref,
            LockingTestingPayload::default(),
        );
        let ret = lock_4.ordered_try_write(&stroad, 3);
        assert_eq!(ret, Ok(false));
        assert_eq!(unsafe { *obj_ref.ptr.num_rw.get() }, 0x8000000000000001);

        unsafe {
            lock_0.unlock(&stroad);
            // shouldn't unpark anything yet
            assert_eq!(*obj_ref.ptr.num_rw.get(), 0x8000000000000000);
            assert!(!(*lock_2.stroad_state.get()).payload.unparked);
            assert!(!(*lock_3.stroad_state.get()).payload.unparked);
            assert!(!(*lock_4.stroad_state.get()).payload.unparked);

            lock_1.unlock(&stroad);
            assert_eq!(*obj_ref.ptr.num_rw.get(), 0);
            // both of these should now be unparked
            assert!((*lock_2.stroad_state.get()).payload.unparked);
            assert!((*lock_3.stroad_state.get()).payload.unparked);
            // but not this
            assert!(!(*lock_4.stroad_state.get()).payload.unparked);

            // xxx simulate 2 and 3 getting re-acquired
            lock_2.state.set(LockState::Unlocked);
            lock_3.state.set(LockState::Unlocked);
            let ret = lock_2.ordered_try_read(&stroad, 2);
            assert_eq!(ret, Ok(true));
            assert_eq!(*obj_ref.ptr.num_rw.get(), 1);
            let ret = lock_3.ordered_try_read(&stroad, 2);
            assert_eq!(ret, Ok(true));
            assert_eq!(*obj_ref.ptr.num_rw.get(), 2);

            lock_2.unlock(&stroad);
            // shouldn't unpark yet
            assert_eq!(*obj_ref.ptr.num_rw.get(), 1);
            assert!(!(*lock_4.stroad_state.get()).payload.unparked);

            lock_3.unlock(&stroad);
            // now it should
            assert_eq!(*obj_ref.ptr.num_rw.get(), 0);
            assert!((*lock_4.stroad_state.get()).payload.unparked);
        }
    }
}
