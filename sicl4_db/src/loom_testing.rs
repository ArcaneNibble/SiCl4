#[cfg(loom)]
pub use loom::sync::atomic::{AtomicBool, AtomicPtr, AtomicU32, AtomicU64, AtomicUsize};
#[cfg(not(loom))]
pub use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU32, AtomicU64, AtomicUsize};

#[cfg(loom)]
pub use loom::sync::{Condvar, Mutex};
#[cfg(not(loom))]
pub use std::sync::{Condvar, Mutex};

#[cfg(loom)]
pub fn spin_hint() {
    loom::thread::yield_now();
}
#[cfg(not(loom))]
pub fn spin_hint() {
    std::hint::spin_loop();
}
