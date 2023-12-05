use std::sync::{atomic::AtomicUsize, Arc, RwLock, Weak};

use uuid::Uuid;

#[derive(Debug)]
pub struct NetlistCell {
    pub cell_type: Uuid,
    pub debug_id: usize,
    pub visited_marker: bool,
    connections: Vec<Option<Weak<RwLock<Wire>>>>,
}

impl NetlistCell {
    pub fn new(cell_type: Uuid, debug_id: usize, num_connections: usize) -> Self {
        Self {
            cell_type,
            debug_id,
            visited_marker: false,
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
    pub debug_id: usize,
    drivers: Vec<Weak<RwLock<NetlistCell>>>,
    sinks: Vec<Weak<RwLock<NetlistCell>>>,
    bidirs: Vec<Weak<RwLock<NetlistCell>>>,
}

impl Wire {
    pub fn new(debug_id: usize) -> Self {
        Self {
            debug_id,
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
    debug_id: AtomicUsize,
}

impl NetlistModule {
    pub fn new() -> Self {
        Self {
            cells: RwLock::new(Vec::new()),
            wires: RwLock::new(Vec::new()),
            debug_id: AtomicUsize::new(0),
        }
    }

    pub fn add_wire(&self) -> Weak<RwLock<Wire>> {
        let wire_debug_id = self
            .debug_id
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let wire = Arc::new(RwLock::new(Wire::new(wire_debug_id)));
        let wire_ref = Arc::downgrade(&wire);
        self.wires.write().unwrap().push(wire);
        wire_ref
    }

    pub fn add_cell(&self, cell_type: Uuid, num_connections: usize) -> Weak<RwLock<NetlistCell>> {
        let cell_debug_id = self
            .debug_id
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let cell = Arc::new(RwLock::new(NetlistCell::new(
            cell_type,
            cell_debug_id,
            num_connections,
        )));
        let cell_ref = Arc::downgrade(&cell);
        self.cells.write().unwrap().push(cell);
        cell_ref
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::thread;
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

    fn debug_print_simple_netlist(netlist: &NetlistModule) {
        let cells = netlist.cells.read().unwrap();
        for cell in cells.iter() {
            let cell = cell.read().unwrap();
            println!("Cell {}", cell.debug_id);
            if cell.cell_type == TEST_LUT_UUID {
                println!(" LUT");
                for i in 0..4 {
                    if let Some(inp_wire) = &cell.connections[i] {
                        let inp_wire_arc = inp_wire.upgrade().unwrap();
                        let inp_wire = inp_wire_arc.read().unwrap();
                        println!(" inp {}: {}", i, inp_wire.debug_id);
                    } else {
                        println!(" inp {}: -- not connected --", i);
                    }
                }
                let outp_wire = cell.connections[4].as_ref().unwrap();
                let outp_wire_arc = outp_wire.upgrade().unwrap();
                let outp_wire = outp_wire_arc.read().unwrap();
                println!(" outp: {}", outp_wire.debug_id);
            } else {
                println!(" BUF");
                let inp_wire = cell.connections[0].as_ref().unwrap();
                let inp_wire_arc = inp_wire.upgrade().unwrap();
                let inp_wire = inp_wire_arc.read().unwrap();
                println!(" inp: {}", inp_wire.debug_id);
                let outp_wire = cell.connections[1].as_ref().unwrap();
                let outp_wire_arc = outp_wire.upgrade().unwrap();
                let outp_wire = outp_wire_arc.read().unwrap();
                println!(" outp: {}", outp_wire.debug_id);
            }
        }
    }

    #[test]
    fn bench_simple_netlist() {
        const NLUTS: usize = 10;
        const AVG_FANIN: f64 = 3.0;
        const N_INITIAL_WORK: usize = 1;
        const NTHREADS: usize = 1;

        let netlist = Arc::new(NetlistModule::new());
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

        let workqueue = work_queue::Queue::new(NTHREADS, 128);
        {
            let cells_rd = netlist.cells.read().unwrap();
            for _ in 0..N_INITIAL_WORK {
                let luti = rng.gen_range(0..NLUTS);
                let lut = Arc::downgrade(&cells_rd[luti]);
                println!("Initial work item: {}", luti);
                workqueue.push(lut);
            }
        }

        // dbg!(&netlist);
        debug_print_simple_netlist(&netlist);
        let start_mutate = Instant::now();
        let thread_handles = workqueue
            .local_queues()
            .map(|mut local_queue| {
                let netlist = netlist.clone();
                thread::spawn(move || {
                    while let Some(cell) = local_queue.pop() {
                        let outwire = {
                            let cell_arc = cell.upgrade().unwrap();
                            let mut cell_wr = cell_arc.write().unwrap();
                            if cell_wr.visited_marker {
                                continue;
                            }
                            cell_wr.visited_marker = true;
                            // println!("debug: cell is {:?}", cell_wr);

                            if cell_wr.cell_type == TEST_BUF_UUID {
                                let inp_wire_ref = cell_wr.connections[0].as_ref().unwrap();
                                let inp_wire_arc = inp_wire_ref.upgrade().unwrap();
                                let inp_wire = inp_wire_arc.read().unwrap();
                                let driver_cell = &inp_wire.drivers[0];
                                local_queue.push(driver_cell.clone());
                                continue;
                            }

                            for i in 0..4 {
                                if let Some(inp_wire_ref) = &cell_wr.connections[i] {
                                    let inp_wire_arc = inp_wire_ref.upgrade().unwrap();
                                    let inp_wire = inp_wire_arc.read().unwrap();
                                    let driver_cell = &inp_wire.drivers[0];
                                    local_queue.push(driver_cell.clone());
                                }
                            }

                            cell_wr.connections[4].as_ref().unwrap().clone()
                        };

                        let added_buf = netlist.add_cell(TEST_BUF_UUID, 2);
                        let added_wire = netlist.add_wire();

                        NetlistCell::disconnect_driver(&cell, 4);
                        NetlistCell::connect_driver(&cell, 4, &added_wire);
                        NetlistCell::connect_sink(&added_buf, 0, &added_wire);
                        NetlistCell::connect_driver(&added_buf, 1, &outwire);
                    }
                })
            })
            .collect::<Vec<_>>();

        for t in thread_handles {
            t.join().unwrap();
        }
        let mutate_duration = start_mutate.elapsed();
        println!("Mutating netlist took {:?}", mutate_duration);
        // dbg!(&netlist);
        debug_print_simple_netlist(&netlist);
    }
}
