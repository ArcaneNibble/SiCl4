use std::{error::Error, fmt::Display};

use pyo3::prelude::*;

#[derive(Debug)]
enum ReplError {
    PythonError(PyErr),
    IoError(std::io::Error),
}

impl Display for ReplError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplError::PythonError(e) => write!(f, "python error: {}", e),
            ReplError::IoError(e) => write!(f, "io error: {}", e)
        }
    }
}

impl Error for ReplError {}

impl From<PyErr> for ReplError {
    fn from(value: PyErr) -> Self {
        Self::PythonError(value)
    }
}

impl From<std::io::Error> for ReplError {
    fn from(value: std::io::Error) -> Self {
        Self::IoError(value)
    }
}

fn main() -> Result<(), ReplError> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() == 1 {
        Python::with_gil(|py| {
            py.run("import code; code.interact('Welcome to SiCl4 Python REPL!')", None, None)
        })?;
    } else {
        let fn_to_load = &args[1];
        let code = std::fs::read_to_string(fn_to_load)?;
        Python::with_gil(|py| -> PyResult<()>{
            PyModule::from_code(py, &code, fn_to_load, "__main__")?;
            Ok(())
        })?;
    }
    Ok(())
}
