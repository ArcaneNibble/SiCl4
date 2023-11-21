use std::io::{Read, Write};

use bson::SerializerOptions;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Db {
    test: String,
}

impl Db {
    pub fn new() -> Self {
        Self {
            test: "hello world".to_owned(),
        }
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
