//! Netlist data model

use std::ops::DerefMut;

use crate::{executor_engine::NetlistGuard, lock_ops::*};

use uuid::Uuid;

/// Cells in a netlist
#[derive(Debug)]
pub struct NetlistCell<'arena> {
    // todo
    pub(crate) cell_type: Uuid,
    pub(crate) debug_id: usize,
    pub(crate) visited_marker: bool,
    pub(crate) connections: Vec<Option<NetlistWireRef<'arena>>>,
}
pub type NetlistCellRef<'arena> = ObjRef<'arena, NetlistCell<'arena>>;
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
    pub(crate) debug_id: usize,
    pub(crate) drivers: Vec<NetlistCellRef<'arena>>,
    pub(crate) sinks: Vec<NetlistCellRef<'arena>>,
    pub(crate) bidirs: Vec<NetlistCellRef<'arena>>,
}
pub type NetlistWireRef<'arena> = ObjRef<'arena, NetlistWire<'arena>>;
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

pub fn connect_driver<'guard, 'arena>(
    cell: &'guard mut (impl DerefMut<Target = NetlistCell<'arena>>
                     + NetlistGuard<'arena, NetlistCell<'arena>>),
    conn_idx: usize,
    wire: &'guard mut (impl DerefMut<Target = NetlistWire<'arena>>
                     + NetlistGuard<'arena, NetlistWire<'arena>>),
) {
    cell.connections[conn_idx] = Some(wire.ref_());
    wire.drivers.push(cell.ref_());
}
pub fn connect_sink<'guard, 'arena>(
    cell: &'guard mut (impl DerefMut<Target = NetlistCell<'arena>>
                     + NetlistGuard<'arena, NetlistCell<'arena>>),
    conn_idx: usize,
    wire: &'guard mut (impl DerefMut<Target = NetlistWire<'arena>>
                     + NetlistGuard<'arena, NetlistWire<'arena>>),
) {
    cell.connections[conn_idx] = Some(wire.ref_());
    wire.sinks.push(cell.ref_());
}
pub fn connect_bidir<'guard, 'arena>(
    cell: &'guard mut (impl DerefMut<Target = NetlistCell<'arena>>
                     + NetlistGuard<'arena, NetlistCell<'arena>>),
    conn_idx: usize,
    wire: &'guard mut (impl DerefMut<Target = NetlistWire<'arena>>
                     + NetlistGuard<'arena, NetlistWire<'arena>>),
) {
    cell.connections[conn_idx] = Some(wire.ref_());
    wire.bidirs.push(cell.ref_());
}
pub fn disconnect_driver<'guard, 'arena>(
    cell: &'guard mut (impl DerefMut<Target = NetlistCell<'arena>>
                     + NetlistGuard<'arena, NetlistCell<'arena>>),
    conn_idx: usize,
    wire: &'guard mut (impl DerefMut<Target = NetlistWire<'arena>>
                     + NetlistGuard<'arena, NetlistWire<'arena>>),
) {
    let ref_wire_idx = cell.connections[conn_idx].take();
    assert_eq!(ref_wire_idx, Some(wire.ref_()));
    let wire_to_cell_idx = wire
        .drivers
        .iter()
        .position(|wire_to_cell| cell.ref_() == *wire_to_cell)
        .unwrap();
    wire.drivers.swap_remove(wire_to_cell_idx);
}
pub fn disconnect_sink<'guard, 'arena>(
    cell: &'guard mut (impl DerefMut<Target = NetlistCell<'arena>>
                     + NetlistGuard<'arena, NetlistCell<'arena>>),
    conn_idx: usize,
    wire: &'guard mut (impl DerefMut<Target = NetlistWire<'arena>>
                     + NetlistGuard<'arena, NetlistWire<'arena>>),
) {
    let ref_wire_idx = cell.connections[conn_idx].take();
    assert_eq!(ref_wire_idx, Some(wire.ref_()));
    let wire_to_cell_idx = wire
        .sinks
        .iter()
        .position(|wire_to_cell| cell.ref_() == *wire_to_cell)
        .unwrap();
    wire.sinks.swap_remove(wire_to_cell_idx);
}
pub fn disconnect_bidir<'guard, 'arena>(
    cell: &'guard mut (impl DerefMut<Target = NetlistCell<'arena>>
                     + NetlistGuard<'arena, NetlistCell<'arena>>),
    conn_idx: usize,
    wire: &'guard mut (impl DerefMut<Target = NetlistWire<'arena>>
                     + NetlistGuard<'arena, NetlistWire<'arena>>),
) {
    let ref_wire_idx = cell.connections[conn_idx].take();
    assert_eq!(ref_wire_idx, Some(wire.ref_()));
    let wire_to_cell_idx = wire
        .bidirs
        .iter()
        .position(|wire_to_cell| cell.ref_() == *wire_to_cell)
        .unwrap();
    wire.bidirs.swap_remove(wire_to_cell_idx);
}
