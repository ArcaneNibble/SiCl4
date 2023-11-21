use std::{
    fs::File,
    sync::{Arc, RwLock},
};

use pyo3::{exceptions::PyIOError, prelude::*};
use uuid::Uuid;

#[pyclass(module = "sicl4")]
struct Module {
    db: Py<Db>,
    uuid: Uuid,
}

#[pymethods]
impl Module {
    fn add_port(&self, name: &str, width: Option<u64>) {
        Python::with_gil(|py| {
            let db_py = self.db.borrow(py);
            let mut db = db_py.inner.write().unwrap();
            let module = db.get_module_mut(self.uuid).unwrap();
            let port = sicl4_db::Port {
                width: width.unwrap_or(1),
            };
            module.add_port(name, port);
        })
    }
}

#[pyclass(module = "sicl4")]
struct Db {
    inner: Arc<RwLock<sicl4_db::Db>>,
}

#[pymethods]
impl Db {
    #[new]
    fn new() -> Self {
        Self {
            inner: Arc::new(RwLock::new(sicl4_db::Db::new())),
        }
    }

    fn add_module(self_: Py<Self>, name: &str) -> Module {
        Python::with_gil(|py| {
            let (uuid, _) = self_.borrow_mut(py).inner.write().unwrap().add_module(name);
            Module { db: self_, uuid }
        })
    }

    #[staticmethod]
    fn load_json(filename: &str) -> PyResult<Self> {
        let file = File::open(filename)?;
        let inner = sicl4_db::Db::load_json(file)
            .map_err(|err| -> PyErr { PyIOError::new_err(format!("{}", err)) })?;
        Ok(Self {
            inner: Arc::new(RwLock::new(inner)),
        })
    }

    #[staticmethod]
    fn load_bson(filename: &str) -> PyResult<Self> {
        let file = File::open(filename)?;
        let inner = sicl4_db::Db::load_bson(file)
            .map_err(|err| -> PyErr { PyIOError::new_err(format!("{}", err)) })?;
        Ok(Self {
            inner: Arc::new(RwLock::new(inner)),
        })
    }

    fn save_json(&self, filename: &str) -> PyResult<()> {
        let file = File::create(filename)?;
        self.inner
            .read()
            .unwrap()
            .save_json(file)
            .map_err(|err| -> PyErr { PyIOError::new_err(format!("{}", err)) })
    }

    fn save_bson(&self, filename: &str) -> PyResult<()> {
        let file = File::create(filename)?;
        self.inner
            .read()
            .unwrap()
            .save_bson(file)
            .map_err(|err| -> PyErr { PyIOError::new_err(format!("{}", err)) })
    }
}

#[pymodule]
#[pyo3(name = "sicl4")]
pub fn sicl4_py_module(_py: Python<'_>, m: &PyModule) -> PyResult<()> {
    m.add_class::<Db>()?;
    Ok(())
}
