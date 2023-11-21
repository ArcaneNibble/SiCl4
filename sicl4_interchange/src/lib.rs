use std::{collections::HashMap, fs::File, path::Path};

use yosys_netlist_json::BitVal;

pub fn import_yosys_json<P: AsRef<Path>>(db: &mut sicl4_db::Db, path: P) {
    // FIXME error handling!
    let reader = File::open(path).unwrap();
    let imported_yosys = yosys_netlist_json::Netlist::from_reader(reader).unwrap();
    for (mod_name, y_module) in imported_yosys.modules.iter() {
        let (_, s_module) = db.add_module(mod_name);
        println!("Importing module {}", mod_name);

        // XXX this needs a total rewrite
        let mut yosys_idx_to_name: HashMap<usize, String> = HashMap::new();

        for (port_name, y_port_info) in y_module.ports.iter() {
            assert!(y_port_info.bits.len() == 1);
            if let BitVal::N(wire_idx) = y_port_info.bits[0] {
                println!("Port {} -> {}", wire_idx, port_name);
                yosys_idx_to_name.insert(wire_idx, port_name.to_owned());

                s_module.add_port(
                    port_name,
                    sicl4_db::Port {
                        width: y_port_info.bits.len() as u64,
                    },
                );
            } else {
                todo!()
            }
        }

        for (wire_name, y_wire_info) in y_module.netnames.iter() {
            assert!(y_wire_info.bits.len() == 1);
            if let BitVal::N(wire_idx) = y_wire_info.bits[0] {
                if yosys_idx_to_name.get(&wire_idx).is_some() {
                    continue;
                }

                println!("Wire {} -> {}", wire_idx, wire_name);
                yosys_idx_to_name.insert(wire_idx, wire_name.to_owned());

                s_module.add_inner_wire(
                    wire_name,
                    sicl4_db::InnerWire {
                        width: y_wire_info.bits.len() as u64,
                    },
                );
            } else {
                todo!()
            }
        }

        for (cell_name, y_cell_info) in y_module.cells.iter() {
            let s_cell = s_module.add_cell(cell_name, &y_cell_info.cell_type);
            println!("Cell {} ty {}", cell_name, y_cell_info.cell_type);
            for (port_name, connections) in y_cell_info.connections.iter() {
                for connection in connections {
                    if let BitVal::N(wire_idx) = connection {
                        let wire_name = yosys_idx_to_name.get(wire_idx).unwrap();
                        println!("  port {} -> {}", port_name, wire_name);
                        s_cell.connect_port(port_name, wire_name);
                    } else {
                        todo!()
                    }
                }
            }
        }
    }
}
