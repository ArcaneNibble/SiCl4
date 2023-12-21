use std::sync::{atomic::AtomicUsize, RwLock, RwLockWriteGuard};

use sharded_slab::Slab;
use uuid::Uuid;

#[derive(Debug)]
pub struct NetlistCell {
    pub cell_type: Uuid,
    pub debug_id: usize,
    pub visited_marker: bool,
    connections: Vec<Option<usize>>,
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
}

#[derive(Debug)]
pub struct Wire {
    pub debug_id: usize,
    drivers: Vec<usize>,
    sinks: Vec<usize>,
    bidirs: Vec<usize>,
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
    cells: Slab<RwLock<NetlistCell>>,
    wires: Slab<RwLock<Wire>>,
    debug_id: AtomicUsize,
}

impl NetlistModule {
    pub fn new() -> Self {
        Self {
            cells: Slab::new(),
            wires: Slab::new(),
            debug_id: AtomicUsize::new(0),
        }
    }

    pub fn add_wire(&self) -> usize {
        let wire_debug_id = self
            .debug_id
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let wire = RwLock::new(Wire::new(wire_debug_id));
        let wire_ref = self.wires.insert(wire).unwrap();
        wire_ref
    }

    pub fn add_cell(&self, cell_type: Uuid, num_connections: usize) -> usize {
        let cell_debug_id = self
            .debug_id
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let cell = RwLock::new(NetlistCell::new(cell_type, cell_debug_id, num_connections));
        let cell_ref = self.cells.insert(cell).unwrap();
        cell_ref
    }

    pub fn connect_driver(
        cell: &mut RwLockWriteGuard<NetlistCell>,
        cell_idx: usize,
        idx: usize,
        wire: &mut RwLockWriteGuard<Wire>,
        wire_idx: usize,
    ) {
        cell.connections[idx] = Some(wire_idx);
        wire.drivers.push(cell_idx);
    }

    pub fn connect_sink(
        cell: &mut RwLockWriteGuard<NetlistCell>,
        cell_idx: usize,
        idx: usize,
        wire: &mut RwLockWriteGuard<Wire>,
        wire_idx: usize,
    ) {
        cell.connections[idx] = Some(wire_idx);
        wire.sinks.push(cell_idx);
    }

    pub fn connect_bidir(
        cell: &mut RwLockWriteGuard<NetlistCell>,
        cell_idx: usize,
        idx: usize,
        wire: &mut RwLockWriteGuard<Wire>,
        wire_idx: usize,
    ) {
        cell.connections[idx] = Some(wire_idx);
        wire.bidirs.push(cell_idx);
    }

    pub fn disconnect_driver(
        cell: &mut RwLockWriteGuard<NetlistCell>,
        cell_idx: usize,
        idx: usize,
        wire: &mut RwLockWriteGuard<Wire>,
        wire_idx: usize,
    ) {
        let ref_wire_idx = cell.connections[idx].take();
        assert_eq!(ref_wire_idx, Some(wire_idx));
        let wire_to_cell_idx = wire
            .drivers
            .iter()
            .position(|wire_to_cell| cell_idx == *wire_to_cell)
            .unwrap();
        wire.drivers.swap_remove(wire_to_cell_idx);
    }

    pub fn disconnect_sink(
        cell: &mut RwLockWriteGuard<NetlistCell>,
        cell_idx: usize,
        idx: usize,
        wire: &mut RwLockWriteGuard<Wire>,
        wire_idx: usize,
    ) {
        let ref_wire_idx = cell.connections[idx].take();
        assert_eq!(ref_wire_idx, Some(wire_idx));
        let wire_to_cell_idx = wire
            .sinks
            .iter()
            .position(|wire_to_cell| cell_idx == *wire_to_cell)
            .unwrap();
        wire.sinks.swap_remove(wire_to_cell_idx);
    }

    pub fn disconnect_bidir(
        cell: &mut RwLockWriteGuard<NetlistCell>,
        cell_idx: usize,
        idx: usize,
        wire: &mut RwLockWriteGuard<Wire>,
        wire_idx: usize,
    ) {
        let ref_wire_idx = cell.connections[idx].take();
        assert_eq!(ref_wire_idx, Some(wire_idx));
        let wire_to_cell_idx = wire
            .bidirs
            .iter()
            .position(|wire_to_cell| cell_idx == *wire_to_cell)
            .unwrap();
        wire.bidirs.swap_remove(wire_to_cell_idx);
    }
}

#[cfg(test)]
mod tests {
    use std::thread;
    use std::{sync::Arc, time::Instant};

    use memory_stats::memory_stats;
    use rand::Rng;
    use rand::SeedableRng;
    use uuid::uuid;
    use uuid::Uuid;

    use super::*;

    const TEST_LUT_UUID: Uuid = uuid!("00000000-0000-0000-0000-000000000000");
    const TEST_BUF_UUID: Uuid = uuid!("00000000-0000-0000-0000-000000000001");

    fn _debug_print_slab_netlist(netlist: &mut NetlistModule) {
        for cell in netlist.cells.unique_iter() {
            let cell = cell.read().unwrap();
            println!("Cell {}", cell.debug_id);
            if cell.cell_type == TEST_LUT_UUID {
                println!(" LUT");
                for i in 0..4 {
                    if let Some(inp_wire) = cell.connections[i] {
                        let inp_wire_e = netlist.wires.get(inp_wire).unwrap();
                        let inp_wire = inp_wire_e.read().unwrap();
                        println!(" inp {}: {}", i, inp_wire.debug_id);
                    } else {
                        println!(" inp {}: -- not connected --", i);
                    }
                }
                let outp_wire = cell.connections[4].unwrap();
                let outp_wire_e = netlist.wires.get(outp_wire).unwrap();
                let outp_wire = outp_wire_e.read().unwrap();
                println!(" outp: {}", outp_wire.debug_id);
            } else {
                println!(" BUF");
                let inp_wire = cell.connections[0].unwrap();
                let inp_wire_e = netlist.wires.get(inp_wire).unwrap();
                let inp_wire = inp_wire_e.read().unwrap();
                println!(" inp: {}", inp_wire.debug_id);
                let outp_wire = cell.connections[1].unwrap();
                let outp_wire_e = netlist.wires.get(outp_wire).unwrap();
                let outp_wire = outp_wire_e.read().unwrap();
                println!(" outp: {}", outp_wire.debug_id);
            }
        }
    }

    #[test]
    fn bench_slab_netlist() {
        const NLUTS: usize = 1_000_000;
        const AVG_FANIN: f64 = 3.0;
        const N_INITIAL_WORK: usize = 1000;
        const NTHREADS: usize = 8;

        let mut netlist = Arc::new(NetlistModule::new());
        let mut rng = rand_xorshift::XorShiftRng::seed_from_u64(0);

        let start_create = Instant::now();
        let start_mem = memory_stats().unwrap();
        let mut generate_hax_luts_vec = Vec::new();
        let mut generate_hax_wires_vec = Vec::new();
        for _ in 0..NLUTS {
            let lut = netlist.add_cell(TEST_LUT_UUID, 5);
            let outwire = netlist.add_wire();
            let lut_e = netlist.cells.get(lut).unwrap();
            let mut lut_w = lut_e.write().unwrap();
            let outwire_e = netlist.wires.get(outwire).unwrap();
            let mut outwire_w = outwire_e.write().unwrap();
            NetlistModule::connect_driver(&mut lut_w, lut, 4, &mut outwire_w, outwire);
            generate_hax_luts_vec.push(lut);
            generate_hax_wires_vec.push(outwire);
        }
        for luti in 0..NLUTS {
            let lut = generate_hax_luts_vec[luti];
            for inpi in 0..4 {
                if rng.gen::<f64>() < (AVG_FANIN / 4.0) {
                    let inp_wire_i = rng.gen_range(0..NLUTS);
                    let inp_wire = generate_hax_wires_vec[inp_wire_i];
                    let lut_e = netlist.cells.get(lut).unwrap();
                    let mut lut_w = lut_e.write().unwrap();
                    let inp_wire_e = netlist.wires.get(inp_wire).unwrap();
                    let mut inp_wire_w = inp_wire_e.write().unwrap();
                    NetlistModule::connect_sink(&mut lut_w, lut, inpi, &mut inp_wire_w, inp_wire);
                }
            }
        }
        let create_duration = start_create.elapsed();
        let create_mem = memory_stats().unwrap();
        println!("Creating netlist took {:?}", create_duration);
        println!(
            "Creating netlist took {:?} MB memory",
            (create_mem.physical_mem - start_mem.physical_mem) as f64 / 1024.0 / 1024.0
        );

        let workqueue = work_queue::Queue::new(NTHREADS, 128);
        {
            for _ in 0..N_INITIAL_WORK {
                let luti = rng.gen_range(0..NLUTS);
                let lut = generate_hax_luts_vec[luti];
                // println!("Initial work item: {}", luti);
                workqueue.push(lut);
            }
        }

        // _debug_print_slab_netlist(Arc::get_mut(&mut netlist).unwrap());
        let start_mutate = Instant::now();
        let thread_handles = workqueue
            .local_queues()
            .map(|mut local_queue| {
                let netlist = netlist.clone();
                thread::spawn(move || {
                    while let Some(cell) = local_queue.pop() {
                        let cell_e = netlist.cells.get(cell).unwrap();
                        let cell_w = cell_e.try_write();
                        if cell_w.is_err() {
                            // dbg!("failed to grab self");
                            local_queue.push(cell);
                            continue;
                        }
                        let mut cell_w = cell_w.unwrap();
                        // println!("grabbed cell {}", cell_w.debug_id);
                        if cell_w.visited_marker {
                            continue;
                        }

                        if cell_w.cell_type == TEST_BUF_UUID {
                            let inp_wire_i = cell_w.connections[0].unwrap();
                            let inp_wire_e = netlist.wires.get(inp_wire_i).unwrap();
                            let inp_wire_r = inp_wire_e.try_read();
                            if inp_wire_r.is_err() {
                                // dbg!("failed to grab inp wire for buf");
                                local_queue.push(cell);
                                continue;
                            }
                            let inp_wire_r = inp_wire_r.unwrap();
                            let driver_cell = inp_wire_r.drivers[0];

                            cell_w.visited_marker = true;
                            local_queue.push(driver_cell);
                        } else {
                            // wtf

                            // hack for self-loop
                            let outwire = cell_w.connections[4].unwrap();

                            // grab input wires for read
                            let inp_wire_0_e;
                            let mut inp_wire_0_r = None;
                            if let Some(inp_wire_ref) = cell_w.connections[0] {
                                if inp_wire_ref != outwire {
                                    inp_wire_0_e = Some(netlist.wires.get(inp_wire_ref).unwrap());
                                    let inp_wire_r = inp_wire_0_e.as_ref().unwrap().try_read();
                                    if inp_wire_r.is_err() {
                                        // dbg!("failed to grab inp 0");
                                        local_queue.push(cell);
                                        continue;
                                    }
                                    let inp_wire_r = inp_wire_r.unwrap();
                                    // println!("grabbed wire {}", inp_wire_w.debug_id);
                                    inp_wire_0_r = Some(inp_wire_r);
                                }
                            }
                            let inp_wire_1_e;
                            let mut inp_wire_1_r = None;
                            if let Some(inp_wire_ref) = cell_w.connections[1] {
                                if inp_wire_ref != outwire {
                                    inp_wire_1_e = Some(netlist.wires.get(inp_wire_ref).unwrap());
                                    let inp_wire_r = inp_wire_1_e.as_ref().unwrap().try_read();
                                    if inp_wire_r.is_err() {
                                        // dbg!("failed to grab inp 1");
                                        local_queue.push(cell);
                                        continue;
                                    }
                                    let inp_wire_r = inp_wire_r.unwrap();
                                    // println!("grabbed wire {}", inp_wire_w.debug_id);
                                    inp_wire_1_r = Some(inp_wire_r);
                                }
                            }
                            let inp_wire_2_e;
                            let mut inp_wire_2_r = None;
                            if let Some(inp_wire_ref) = cell_w.connections[2] {
                                if inp_wire_ref != outwire {
                                    inp_wire_2_e = Some(netlist.wires.get(inp_wire_ref).unwrap());
                                    let inp_wire_r = inp_wire_2_e.as_ref().unwrap().try_read();
                                    if inp_wire_r.is_err() {
                                        // dbg!("failed to grab inp 2");
                                        local_queue.push(cell);
                                        continue;
                                    }
                                    let inp_wire_r = inp_wire_r.unwrap();
                                    // println!("grabbed wire {}", inp_wire_w.debug_id);
                                    inp_wire_2_r = Some(inp_wire_r);
                                }
                            }
                            let inp_wire_3_e;
                            let mut inp_wire_3_r = None;
                            if let Some(inp_wire_ref) = cell_w.connections[3] {
                                if inp_wire_ref != outwire {
                                    inp_wire_3_e = Some(netlist.wires.get(inp_wire_ref).unwrap());
                                    let inp_wire_r = inp_wire_3_e.as_ref().unwrap().try_read();
                                    if inp_wire_r.is_err() {
                                        // dbg!("failed to grab inp 3");
                                        local_queue.push(cell);
                                        continue;
                                    }
                                    let inp_wire_r = inp_wire_r.unwrap();
                                    // println!("grabbed wire {}", inp_wire_w.debug_id);
                                    inp_wire_3_r = Some(inp_wire_r);
                                }
                            }

                            // grab output wire for write
                            let outwire_e = netlist.wires.get(outwire).unwrap();
                            let outwire_w = outwire_e.try_write();
                            if outwire_w.is_err() {
                                // dbg!("failed to grab outp");
                                local_queue.push(cell);
                                continue;
                            }
                            let mut outwire_w = outwire_w.unwrap();

                            let added_buf = netlist.add_cell(TEST_BUF_UUID, 2);
                            let added_buf_e = netlist.cells.get(added_buf).unwrap();
                            let mut added_buf_w = added_buf_e.write().unwrap();
                            let added_wire = netlist.add_wire();
                            let added_wire_e = netlist.wires.get(added_wire).unwrap();
                            let mut added_wire_w = added_wire_e.write().unwrap();

                            // actual updates
                            cell_w.visited_marker = true;

                            if let Some(inp_wire_r) = inp_wire_0_r {
                                local_queue.push(inp_wire_r.drivers[0]);
                            }
                            if let Some(inp_wire_r) = inp_wire_1_r {
                                local_queue.push(inp_wire_r.drivers[0]);
                            }
                            if let Some(inp_wire_r) = inp_wire_2_r {
                                local_queue.push(inp_wire_r.drivers[0]);
                            }
                            if let Some(inp_wire_r) = inp_wire_3_r {
                                local_queue.push(inp_wire_r.drivers[0]);
                            }

                            // xxx this is an ad-hoc clusterfuck
                            let outwire_backlink_idx = outwire_w
                                .drivers
                                .iter()
                                .position(|wire_to_cell| cell == *wire_to_cell)
                                .unwrap();

                            outwire_w.drivers[outwire_backlink_idx] = added_buf;
                            added_buf_w.connections[1] = Some(outwire);

                            added_buf_w.connections[0] = Some(added_wire);
                            added_wire_w.sinks.push(added_buf);

                            cell_w.connections[4] = Some(added_wire);
                            added_wire_w.drivers.push(cell);
                        }
                    }
                })
            })
            .collect::<Vec<_>>();

        for t in thread_handles {
            t.join().unwrap();
        }
        let mutate_duration = start_mutate.elapsed();
        let mutate_ram = memory_stats().unwrap();
        println!("Mutating netlist took {:?}", mutate_duration);
        println!(
            "Final additional usage {:?} MB memory",
            (mutate_ram.physical_mem - start_mem.physical_mem) as f64 / 1024.0 / 1024.0
        );
        // _debug_print_slab_netlist(Arc::get_mut(&mut netlist).unwrap());
    }
}
