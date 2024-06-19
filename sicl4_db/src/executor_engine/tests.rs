use std::time::Instant;

use super::*;
use memory_stats::memory_stats;
use rand::{Rng, SeedableRng};
use uuid::uuid;

const TEST_LUT_UUID: Uuid = uuid!("00000000-0000-0000-0000-000000000000");
const TEST_BUF_UUID: Uuid = uuid!("00000000-0000-0000-0000-000000000001");

#[test]
fn executor_ensure_obj_safety() {
    let _x: &dyn UnorderedAlgorithm<ROtoRWTy = u32>;
}

#[cfg(not(loom))]
#[test]
#[should_panic]
fn executor_single_threaded_only_one() {
    let manager = NetlistManager::new();
    let workqueue = work_queue::Queue::new(1, 128);
    let _view1 = manager.access_single_threaded(&workqueue);
    let _view2 = manager.access_single_threaded(&workqueue);
}

#[cfg(not(loom))]
#[test]
fn executor_single_threaded_smoke_test() {
    let manager = NetlistManager::new();
    let workqueue = work_queue::Queue::new(1, 128);
    let mut view = manager.access_single_threaded(&workqueue);
    let cell_ref;
    let wire_ref;
    {
        let mut cell = view.new_cell((), TEST_LUT_UUID, 1);
        dbg!(&cell);
        dbg!(&*cell);
        cell_ref = cell.x;
        let mut wire = view.new_wire(());
        dbg!(&wire);
        dbg!(&*wire);
        wire_ref = wire.x;
        view.add_work(cell_ref.into());

        connect_driver(&mut cell, 0, &mut wire);
    }
    {
        let cell_again = view.get_cell_read((), cell_ref).unwrap();
        let wire_again = view.get_wire_read((), wire_ref).unwrap();
        assert_eq!(cell_again.connections[0], Some(wire_ref));
        assert_eq!(wire_again.drivers[0], cell_ref);
        view.delete_cell(cell_again);
        view.delete_wire(wire_again);
    }
    {
        let cell_again_again = view.get_cell_read((), cell_ref);
        let wire_again_again = view.get_wire_read((), wire_ref);
        assert!(cell_again_again.is_none());
        assert!(wire_again_again.is_none());
    }
}

#[cfg(not(loom))]
#[test]
fn executor_single_threaded_only_one_get() {
    let manager = NetlistManager::new();
    let workqueue = work_queue::Queue::new(1, 128);
    let mut view = manager.access_single_threaded(&workqueue);
    let cell = view.new_cell((), TEST_LUT_UUID, 0);
    let cell_ref = cell.x;
    drop(cell);

    let cell_again_0 = view.get_cell_read((), cell_ref);
    let cell_again_1 = view.get_cell_read((), cell_ref);
    assert!(cell_again_0.is_some());
    assert!(cell_again_1.is_none());
}

#[cfg(not(loom))]
#[test]
fn executor_asdf() {
    let manager = NetlistManager::new();
    let workqueue = work_queue::Queue::new(1, 128);
    let mut view = manager.access_single_threaded(&workqueue);
    let cell = view.new_cell((), TEST_LUT_UUID, 0);
    dbg!(&cell);
    dbg!(&*cell);
    let wire = view.new_wire(());
    dbg!(&wire);
    dbg!(&*wire);
    view.add_work(cell.x.into());
    drop(view);
    let cell_ref = cell.x;
    drop(cell);

    let mut view = manager.access_single_threaded(&workqueue);
    let cell2 = view.get_cell_read((), cell_ref);
    dbg!(&cell2);
    let cell3 = view.get_cell_read((), cell_ref);
    dbg!(&cell3);
}

#[cfg(not(loom))]
#[test]
fn executor_asdf2() {
    struct TestAlgo {}
    impl UnorderedAlgorithm for TestAlgo {
        type ROtoRWTy = ();

        fn try_process_readonly<'algo_global_state, 'view, 'arena>(
            &'algo_global_state self,
            view: &'view mut UnorderedAlgorithmROView<'arena>,
            work_item: &'arena WorkItem<'arena, 'arena>,
        ) -> Result<Self::ROtoRWTy, ()> {
            dbg!(work_item.seed_node);
            let x = view.try_lock_cell(work_item, work_item.seed_node.cell(), true)?;
            dbg!(&*x);
            let y = view.try_lock_wire(work_item, x.connections[0].unwrap(), false)?;
            dbg!(&*y);
            Ok(())
        }

        fn process_finish_readwrite<'algo_state, 'view, 'arena, 'q>(
            &'algo_state self,
            view: &'view mut UnorderedAlgorithmRWView<'arena, 'q>,
            work_item: &'arena WorkItem<'arena, 'arena>,
            _ro_output: Self::ROtoRWTy,
        ) {
            dbg!(work_item.seed_node);
            let x = view
                .get_cell_write(work_item, work_item.seed_node.cell())
                .unwrap();
            dbg!(&*x);
            let y = view
                .get_wire_read(work_item, x.connections[0].unwrap())
                .unwrap();
            dbg!(&*y);
        }
    }

    let manager = NetlistManager::new();
    let workqueue = work_queue::Queue::new(1, 128);
    let mut view = manager.access_single_threaded(&workqueue);
    let mut cell = view.new_cell((), TEST_LUT_UUID, 1);
    let mut wire = view.new_wire(());
    connect_driver(&mut cell, 0, &mut wire);
    view.add_work(cell.x.into());
    drop(view);
    drop(cell);
    drop(wire);

    let algo = TestAlgo {};
    manager.run_unordered_algorithm(&algo, &workqueue);
}

#[test]
fn bench_full_custom_netlist() {
    const NLUTS: usize = 1_000_000;
    const AVG_FANIN: f64 = 3.0;
    const N_INITIAL_WORK: usize = 1000;
    const NTHREADS: usize = 8;

    let manager = NetlistManager::new();
    let workqueue = work_queue::Queue::new(NTHREADS, 128);
    let start_mem = memory_stats().unwrap();

    {
        let mut init_thread_view = manager.access_single_threaded(&workqueue);
        let mut rng = rand_xorshift::XorShiftRng::seed_from_u64(0);

        let start_create = Instant::now();
        let mut generate_hax_luts_vec = Vec::new();
        let mut generate_hax_wires_vec = Vec::new();

        for _ in 0..NLUTS {
            let mut lut = init_thread_view.new_cell((), TEST_LUT_UUID, 5);
            let mut outwire = init_thread_view.new_wire(());
            connect_driver(&mut lut, 4, &mut outwire);
            generate_hax_luts_vec.push(lut);
            generate_hax_wires_vec.push(outwire);
        }

        for luti in 0..NLUTS {
            let lut = &mut generate_hax_luts_vec[luti];
            for inpi in 0..4 {
                if rng.gen::<f64>() < (AVG_FANIN / 4.0) {
                    let inp_wire_i = rng.gen_range(0..NLUTS);
                    let inp_wire = &mut generate_hax_wires_vec[inp_wire_i];
                    connect_sink(lut, inpi, inp_wire);
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

        let start_queue = Instant::now();
        {
            for _ in 0..N_INITIAL_WORK {
                let luti = rng.gen_range(0..NLUTS);
                let lut = generate_hax_luts_vec[luti].x;
                init_thread_view.add_work(lut.into());
                // println!("Initial work item: {}", luti);
            }
        }
        let queue_duration = start_queue.elapsed();
        let queue_mem = memory_stats().unwrap();
        println!("Queuing work took {:?}", queue_duration);
        println!(
            "Queuing work took {:?} MB memory",
            (queue_mem.physical_mem - start_mem.physical_mem) as f64 / 1024.0 / 1024.0
        );
    }

    struct BenchmarkAlgo {}
    impl UnorderedAlgorithm for BenchmarkAlgo {
        type ROtoRWTy = ();

        fn try_process_readonly<'algo_global_state, 'view, 'arena>(
            &'algo_global_state self,
            view: &'view mut UnorderedAlgorithmROView<'arena>,
            work_item: &'arena WorkItem<'arena, 'arena>,
        ) -> Result<Self::ROtoRWTy, ()> {
            let cell = work_item.seed_node.cell();
            // println!("RO! {:?}", cell);
            let cell = view.try_lock_cell(work_item, cell, true)?;
            // println!("grabbed cell {}", cell.debug_id);
            if cell.visited_marker {
                return Ok(());
            }

            if cell.cell_type == TEST_BUF_UUID {
                let inp_wire_ref = cell.connections[0].unwrap();
                let _inp_wire = view.try_lock_wire(work_item, inp_wire_ref, false)?;
            } else {
                // hack for self-loop
                let outwire_ref = cell.connections[4].unwrap();

                // grab input wires for read
                let mut inp_wires = [None, None, None, None];
                for inp_i in 0..4 {
                    if let Some(inp_wire_ref) = cell.connections[inp_i] {
                        if inp_wire_ref != outwire_ref {
                            let inp_wire = view.try_lock_wire(work_item, inp_wire_ref, false)?;
                            // println!("grabbed wire {}", inp_wire.debug_id);
                            inp_wires[inp_i] = Some(inp_wire);
                        }
                    }
                }

                // grab output wire for write
                let _outwire = view.try_lock_wire(work_item, outwire_ref, true)?;
            }

            Ok(())
        }

        fn process_finish_readwrite<'algo_state, 'view, 'arena, 'q>(
            &'algo_state self,
            view: &'view mut UnorderedAlgorithmRWView<'arena, 'q>,
            work_item: &'arena WorkItem<'arena, 'arena>,
            _ro_output: Self::ROtoRWTy,
        ) {
            let cell = work_item.seed_node.cell();
            // println!("RW! {:?}", cell);
            let mut cell = view.get_cell_write(work_item, cell).unwrap();
            // println!("grabbed cell {}", cell.debug_id);
            if cell.visited_marker {
                return;
            }
            // fixme oh noes code dup

            if cell.cell_type == TEST_BUF_UUID {
                let inp_wire_ref = cell.connections[0].unwrap();
                let inp_wire = view.get_wire_read(work_item, inp_wire_ref).unwrap();

                let driver_cell_ref = inp_wire.drivers[0];
                cell.visited_marker = true;
                view.add_work(driver_cell_ref.into());
            } else {
                // hack for self-loop
                let outwire_ref = cell.connections[4].unwrap();

                // grab input wires for read
                let mut inp_wires = [None, None, None, None];
                for inp_i in 0..4 {
                    if let Some(inp_wire_ref) = cell.connections[inp_i] {
                        if inp_wire_ref != outwire_ref {
                            let inp_wire = view.get_wire_read(work_item, inp_wire_ref).unwrap();
                            // println!("grabbed wire {}", inp_wire.debug_id);
                            inp_wires[inp_i] = Some(inp_wire);
                        }
                    }
                }

                // grab output wire for write
                let mut outwire = view.get_wire_write(work_item, outwire_ref).unwrap();

                let mut added_buf = view.new_cell(work_item, TEST_BUF_UUID, 2);
                let mut added_wire = view.new_wire(work_item);

                // actual updates
                cell.visited_marker = true;

                for inp_wire in &inp_wires {
                    if let Some(inp_wire) = inp_wire {
                        view.add_work(inp_wire.drivers[0].into());
                    }
                }

                // xxx this is an ad-hoc clusterfuck
                let outwire_backlink_idx = outwire
                    .drivers
                    .iter()
                    .position(|wire_to_cell| cell.x == *wire_to_cell)
                    .unwrap();

                outwire.drivers[outwire_backlink_idx] = added_buf.x;
                added_buf.connections[1] = Some(outwire_ref);

                added_buf.connections[0] = Some(added_wire.x);
                added_wire.sinks.push(added_buf.x);

                cell.connections[4] = Some(added_wire.x);
                added_wire.drivers.push(cell.x);
            }
        }
    }

    let start_mutate = Instant::now();
    let algo = BenchmarkAlgo {};
    manager.run_unordered_algorithm(&algo, &workqueue);
    let mutate_duration = start_mutate.elapsed();
    let mutate_ram = memory_stats().unwrap();
    println!("Mutating netlist took {:?}", mutate_duration);
    println!(
        "Final additional usage {:?} MB memory",
        (mutate_ram.physical_mem - start_mem.physical_mem) as f64 / 1024.0 / 1024.0
    );
}
