//! Core of the custom netlist data structure
//!
//! This contains TODO not-written-yet logic for handling the netlist data structure itself

use std::fmt::Debug;

use crate::lock_ops::ObjRef;

/// Guards (which are implemented in executor_engine) must allow for extracting the target ptr
pub trait NetlistGuard<'arena, T> {
    fn ref_<'guard>(&'guard self) -> ObjRef<'arena, T>;
}

/// Cells in a netlist
#[derive(Debug)]
pub struct NetlistCell<'arena> {
    // todo
    _wire: Option<NetlistWireRef<'arena>>,
}
pub type NetlistCellRef<'arena> = ObjRef<'arena, NetlistCell<'arena>>;
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
pub type NetlistWireRef<'arena> = ObjRef<'arena, NetlistWire<'arena>>;
impl<'arena> NetlistWire<'arena> {
    pub unsafe fn init(self_: *mut Self) -> &'arena mut Self {
        (*self_)._cell = None;

        // safety: assert that we initialized everything
        &mut *self_
    }
}
