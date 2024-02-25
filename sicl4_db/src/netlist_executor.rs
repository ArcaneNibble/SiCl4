//! Manages a netlist and running algorithms on it

use std::alloc::Layout;

use crate::{allocator::*, locking::*, netlist::*};

/// Top-level netlist + work items unified data structure
///
/// This doesn't actually *have* to be unified, but it's simpler this way
#[derive(Debug)]
pub struct NetlistManager<'arena> {
    heap: SlabRoot<'arena, NetlistTypeMapper>,
}
impl<'arena> NetlistManager<'arena> {
    /// Construct a new unified data structure
    pub fn new() -> Self {
        Self {
            heap: SlabRoot::new(),
        }
    }
    /// Get a thread shard for performing operations on the netlist
    pub fn new_thread(&'arena self) -> NetlistManagerThread<'arena> {
        NetlistManagerThread {
            heap_shard: self.heap.new_thread(),
        }
    }
}

/// Separate cells/wires/work items into separate type bins
struct NetlistTypeMapper {}
impl TypeMapper for NetlistTypeMapper {
    type BinsArrayTy<T> = [T; 2];
    const LAYOUTS: &'static [&'static [Layout]] = &[
        &[Layout::new::<LockedObj<NetlistCell>>()],
        &[Layout::new::<LockedObj<NetlistWire>>()],
    ];
}
impl<'arena> TypeMappable<NetlistTypeMapper> for LockedObj<NetlistCell<'arena>> {
    const I: usize = 0;
}
impl<'arena> TypeMappable<NetlistTypeMapper> for LockedObj<NetlistWire<'arena>> {
    const I: usize = 1;
}

/// Provides one thread with access to the netlist
#[derive(Debug)]
pub struct NetlistManagerThread<'arena> {
    heap_shard: SlabThreadShard<'arena, NetlistTypeMapper>,
}

impl<'arena> NetlistManagerThread<'arena> {}
