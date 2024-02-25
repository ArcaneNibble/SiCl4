#[cfg(loom)]
pub use loom::sync::atomic::{AtomicPtr, AtomicU64, AtomicUsize};
#[cfg(not(loom))]
pub use std::sync::atomic::{AtomicPtr, AtomicU64, AtomicUsize};

#[cfg(loom)]
pub fn spin_hint() {
    loom::thread::yield_now();
}
#[cfg(not(loom))]
pub fn spin_hint() {
    std::hint::spin_loop();
}
