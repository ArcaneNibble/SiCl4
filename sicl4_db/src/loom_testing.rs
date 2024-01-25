#[cfg(loom)]
pub use loom::sync::atomic::{AtomicPtr, AtomicU64, AtomicUsize};
#[cfg(not(loom))]
pub use std::sync::atomic::{AtomicPtr, AtomicU64, AtomicUsize};
