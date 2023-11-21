use std::{fs::File, sync::Arc};

use pyo3::{exceptions::PyIOError, prelude::*};

#[pyclass(module = "sicl4")]
struct Db {
    // todo
    inner: Arc<sicl4_db::Db>,
}

#[pymethods]
impl Db {
    #[new]
    fn new() -> Self {
        Self {
            inner: Arc::new(sicl4_db::Db::new()),
        }
    }

    fn save_json(&self, filename: &str) -> PyResult<()> {
        let file = File::create(filename)?;
        self.inner
            .save_json(file)
            .map_err(|err| -> PyErr { PyIOError::new_err(format!("{}", err)) })
    }

    fn save_bson(&self, filename: &str) -> PyResult<()> {
        let file = File::create(filename)?;
        self.inner
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
