use std::sync::{Arc, RwLock, Weak};

use uuid::Uuid;

#[derive(Debug)]
pub struct NetlistCell {
    pub cell_type: Uuid,
    connections: Vec<Option<Weak<RwLock<Wire>>>>,
}

impl NetlistCell {
    pub fn new(cell_type: Uuid, num_connections: usize) -> Self {
        Self {
            cell_type,
            connections: vec![None; num_connections],
        }
    }

    pub fn connect_driver(self_: &Weak<RwLock<Self>>, idx: usize, wire_: &Weak<RwLock<Wire>>) {
        let cell_arc = self_.upgrade().unwrap();
        let mut cell = cell_arc.write().unwrap();
        let wire_arc = wire_.upgrade().unwrap();
        let mut wire = wire_arc.write().unwrap();
        cell.connections[idx] = Some(wire_.clone());
        wire.drivers.push(self_.clone());
    }

    pub fn connect_sink(self_: &Weak<RwLock<Self>>, idx: usize, wire_: &Weak<RwLock<Wire>>) {
        let cell_arc = self_.upgrade().unwrap();
        let mut cell = cell_arc.write().unwrap();
        let wire_arc = wire_.upgrade().unwrap();
        let mut wire = wire_arc.write().unwrap();
        cell.connections[idx] = Some(wire_.clone());
        wire.sinks.push(self_.clone());
    }

    pub fn connect_bidir(self_: &Weak<RwLock<Self>>, idx: usize, wire_: &Weak<RwLock<Wire>>) {
        let cell_arc = self_.upgrade().unwrap();
        let mut cell = cell_arc.write().unwrap();
        let wire_arc = wire_.upgrade().unwrap();
        let mut wire = wire_arc.write().unwrap();
        cell.connections[idx] = Some(wire_.clone());
        wire.bidirs.push(self_.clone());
    }

    pub fn disconnect_driver(self_: &Weak<RwLock<Self>>, idx: usize) {
        let cell_arc = self_.upgrade().unwrap();
        let mut cell = cell_arc.write().unwrap();

        if let Some(wire_) = cell.connections[idx].take() {
            let wire_arc = wire_.upgrade().unwrap();
            let mut wire = wire_arc.write().unwrap();
            let wire_to_cell_idx = wire
                .drivers
                .iter()
                .position(|wire_to_cell| Weak::ptr_eq(self_, wire_to_cell))
                .unwrap();
            wire.drivers.swap_remove(wire_to_cell_idx);
        }
    }

    pub fn disconnect_sink(self_: &Weak<RwLock<Self>>, idx: usize) {
        let cell_arc = self_.upgrade().unwrap();
        let mut cell = cell_arc.write().unwrap();

        if let Some(wire_) = cell.connections[idx].take() {
            let wire_arc = wire_.upgrade().unwrap();
            let mut wire = wire_arc.write().unwrap();
            let wire_to_cell_idx = wire
                .sinks
                .iter()
                .position(|wire_to_cell| Weak::ptr_eq(self_, wire_to_cell))
                .unwrap();
            wire.sinks.swap_remove(wire_to_cell_idx);
        }
    }

    pub fn disconnect_bidir(self_: &Weak<RwLock<Self>>, idx: usize) {
        let cell_arc = self_.upgrade().unwrap();
        let mut cell = cell_arc.write().unwrap();

        if let Some(wire_) = cell.connections[idx].take() {
            let wire_arc = wire_.upgrade().unwrap();
            let mut wire = wire_arc.write().unwrap();
            let wire_to_cell_idx = wire
                .bidirs
                .iter()
                .position(|wire_to_cell| Weak::ptr_eq(self_, wire_to_cell))
                .unwrap();
            wire.bidirs.swap_remove(wire_to_cell_idx);
        }
    }
}

#[derive(Debug)]
pub struct Wire {
    drivers: Vec<Weak<RwLock<NetlistCell>>>,
    sinks: Vec<Weak<RwLock<NetlistCell>>>,
    bidirs: Vec<Weak<RwLock<NetlistCell>>>,
}

impl Wire {
    pub fn new() -> Self {
        Self {
            drivers: Vec::new(),
            sinks: Vec::new(),
            bidirs: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub struct NetlistModule {
    cells: RwLock<Vec<Arc<RwLock<NetlistCell>>>>,
    wires: RwLock<Vec<Arc<RwLock<Wire>>>>,
}

impl NetlistModule {
    pub fn new() -> Self {
        Self {
            cells: RwLock::new(Vec::new()),
            wires: RwLock::new(Vec::new()),
        }
    }

    pub fn add_wire(&self) -> Weak<RwLock<Wire>> {
        let wire = Arc::new(RwLock::new(Wire::new()));
        let wire_ref = Arc::downgrade(&wire);
        self.wires.write().unwrap().push(wire);
        wire_ref
    }

    pub fn add_cell(&self, cell_type: Uuid, num_connections: usize) -> Weak<RwLock<NetlistCell>> {
        let cell = Arc::new(RwLock::new(NetlistCell::new(cell_type, num_connections)));
        let cell_ref = Arc::downgrade(&cell);
        self.cells.write().unwrap().push(cell);
        cell_ref
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::time::Instant;

    use rand::{Rng, SeedableRng};
    use uuid::uuid;
    use uuid::Uuid;

    use super::{NetlistCell, NetlistModule};

    const TEST_LUT_UUID: Uuid = uuid!("00000000-0000-0000-0000-000000000000");
    const TEST_BUF_UUID: Uuid = uuid!("00000000-0000-0000-0000-000000000001");

    #[test]
    fn test_simple_netlist() {
        let netlist = NetlistModule::new();

        let wire1 = netlist.add_wire();
        let wire2 = netlist.add_wire();

        let cell1 = netlist.add_cell(TEST_LUT_UUID, 2);
        let cell2 = netlist.add_cell(TEST_BUF_UUID, 2);

        NetlistCell::connect_driver(&cell1, 0, &wire1);
        NetlistCell::connect_sink(&cell1, 1, &wire2);

        NetlistCell::connect_driver(&cell2, 0, &wire2);
        NetlistCell::connect_sink(&cell2, 1, &wire1);

        dbg!(&netlist);

        NetlistCell::disconnect_driver(&cell1, 0);
        dbg!(&netlist);
        NetlistCell::disconnect_driver(&cell2, 0);
        dbg!(&netlist);
        NetlistCell::disconnect_sink(&cell1, 1);
        dbg!(&netlist);
        NetlistCell::disconnect_sink(&cell2, 1);
        dbg!(&netlist);
    }

    #[test]
    fn bench_simple_netlist() {
        const NLUTS: usize = 1000;
        const AVG_FANIN: f64 = 3.0;

        let netlist = NetlistModule::new();
        let mut rng = rand_xorshift::XorShiftRng::seed_from_u64(0);

        let start_create = Instant::now();
        for _ in 0..NLUTS {
            let lut = netlist.add_cell(TEST_LUT_UUID, 5);
            let outwire = netlist.add_wire();
            NetlistCell::connect_driver(&lut, 4, &outwire);
        }
        {
            let cells_wr = netlist.cells.write().unwrap();
            let wires_rd = netlist.wires.read().unwrap();
            for luti in 0..NLUTS {
                let lut = &cells_wr[luti];
                for inpi in 0..4 {
                    if rng.gen::<f64>() < (AVG_FANIN / 4.0) {
                        let inp_wire_i = rng.gen_range(0..NLUTS);
                        let inp_wire = Arc::downgrade(&wires_rd[inp_wire_i]);
                        NetlistCell::connect_sink(&Arc::downgrade(lut), inpi, &inp_wire);
                    }
                }
            }
        }
        let create_duration = start_create.elapsed();
        println!("Creating netlist took {:?}", create_duration);
        // dbg!(&netlist);
    }
}
