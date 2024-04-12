use super::*;

#[test]
fn executor_ensure_obj_safety() {
    let _x: &dyn UnorderedAlgorithm<ROtoRWTy = u32>;
}

#[cfg(not(loom))]
#[test]
#[should_panic]
fn executor_single_threaded_only_one() {
    let manager = NetlistManager::new();
    let _view1 = manager.access_single_threaded();
    let _view2 = manager.access_single_threaded();
}

#[cfg(not(loom))]
#[test]
fn executor_single_threaded_smoke_test() {
    let manager = NetlistManager::new();
    let mut view = manager.access_single_threaded();
    let cell_ref;
    let wire_ref;
    {
        let mut cell = view.new_cell();
        dbg!(&cell);
        dbg!(&*cell);
        cell_ref = cell.x;
        let mut wire = view.new_wire();
        dbg!(&wire);
        dbg!(&*wire);
        wire_ref = wire.x;
        let work_item = view.new_work_item(cell_ref.into());
        dbg!(work_item);

        cell._wire = Some(wire_ref);
        wire._cell = Some(cell_ref);
    }
    {
        let cell_again = view.get_cell(cell_ref).unwrap();
        let wire_again = view.get_wire(wire_ref).unwrap();
        assert_eq!(cell_again._wire, Some(wire_ref));
        assert_eq!(wire_again._cell, Some(cell_ref));
        view.delete_cell(cell_again);
        view.delete_wire(wire_again);
    }
    {
        let cell_again_again = view.get_cell(cell_ref);
        let wire_again_again = view.get_wire(wire_ref);
        assert!(cell_again_again.is_none());
        assert!(wire_again_again.is_none());
    }
}

#[cfg(not(loom))]
#[test]
fn executor_single_threaded_only_one_get() {
    let manager = NetlistManager::new();
    let mut view = manager.access_single_threaded();
    let cell = view.new_cell();
    let cell_ref = cell.x;
    drop(cell);

    let cell_again_0 = view.get_cell(cell_ref);
    let cell_again_1 = view.get_cell(cell_ref);
    assert!(cell_again_0.is_some());
    assert!(cell_again_1.is_none());
}

#[cfg(not(loom))]
#[test]
fn executor_asdf() {
    let manager = NetlistManager::new();
    let mut view = manager.access_single_threaded();
    let cell = view.new_cell();
    dbg!(&cell);
    dbg!(&*cell);
    let wire = view.new_wire();
    dbg!(&wire);
    dbg!(&*wire);
    let work_item = view.new_work_item(cell.x.into());
    dbg!(work_item);
    drop(view);
    let cell_ref = cell.x;
    drop(cell);

    let mut view = manager.access_single_threaded();
    let cell2 = view.get_cell(cell_ref);
    dbg!(&cell2);
    let cell3 = view.get_cell(cell_ref);
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
            Ok(())
        }

        fn process_finish_readwrite<'algo_state, 'view, 'arena>(
            &'algo_state self,
            view: &'view mut UnorderedAlgorithmRWView<'arena>,
            work_item: &'arena WorkItem<'arena, 'arena>,
            _ro_output: Self::ROtoRWTy,
        ) {
            dbg!(work_item.seed_node);
            let x = view.get_cell_write(work_item, work_item.seed_node.cell());
            dbg!(&*x);
        }
    }

    let manager = NetlistManager::new();
    let mut view = manager.access_single_threaded();
    let mut cell = view.new_cell();
    let mut wire = view.new_wire();
    cell._wire = Some(wire.x);
    wire._cell = Some(cell.x);
    let work_item = view.new_work_item(cell.x.into());
    drop(view);
    drop(cell);
    drop(wire);

    let workqueue = work_queue::Queue::new(1, 128);
    workqueue.push(&*work_item);

    let algo = TestAlgo {};
    manager.run_unordered_algorithm(&algo, &workqueue);
}
