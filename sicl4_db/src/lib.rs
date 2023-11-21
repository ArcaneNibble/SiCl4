use std::{
    collections::HashMap,
    io::{Read, Write},
};

use bson::SerializerOptions;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Port {
    pub width: u64,
}

impl Default for Port {
    fn default() -> Self {
        Self { width: 1 }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Module {
    name: String,
    ports: HashMap<String, Port>,
}

impl Module {
    pub fn add_port(&mut self, name: &str, port: Port) {
        self.ports.insert(name.to_owned(), port);
    }
    pub fn get_port(&self, name: &str) -> Option<Port> {
        self.ports.get(name).map(|x| *x)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Db {
    modules: HashMap<Uuid, Module>,
}

impl Db {
    pub fn new() -> Self {
        Self {
            modules: HashMap::new(),
        }
    }

    pub fn add_module(&mut self, name: &str) -> (Uuid, &mut Module) {
        let module = Module {
            name: name.to_owned(),
            ports: HashMap::new(),
        };
        let uuid = Uuid::new_v4();
        self.modules.insert(uuid, module);
        (uuid, self.modules.get_mut(&uuid).unwrap())
    }
    pub fn get_module(&self, uuid: Uuid) -> Option<&Module> {
        self.modules.get(&uuid)
    }
    pub fn get_module_mut(&mut self, uuid: Uuid) -> Option<&mut Module> {
        self.modules.get_mut(&uuid)
    }

    pub fn load_json<R: Read>(r: R) -> serde_json::Result<Self> {
        serde_json::from_reader(r)
    }

    pub fn load_bson<R: Read>(r: R) -> bson::de::Result<Self> {
        bson::from_reader(r)
    }

    pub fn save_json<W: Write>(&self, w: W) -> serde_json::Result<()> {
        serde_json::to_writer(w, self)
    }

    pub fn save_bson<W: Write>(&self, w: W) -> bson::ser::Result<()> {
        let options = SerializerOptions::builder().human_readable(false).build();
        bson::to_bson_with_options(self, options)?
            .as_document()
            .unwrap()
            .to_writer(w)
    }
}
