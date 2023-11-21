use std::{error::Error, fmt::Display};

use pyo3::prelude::*;

#[pyfunction]
fn test_double(x: usize) -> usize {
    x * 2
}

#[pymodule]
#[pyo3(name = "sicl4")]
fn sicl4_py_module(_py: Python<'_>, m: &PyModule) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(test_double, m)?)?;
    Ok(())
}

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
    pyo3::append_to_inittab!(sicl4_py_module);

    let args = std::env::args().collect::<Vec<_>>();
    if args.len() == 1 {
        // https://stackoverflow.com/questions/7116038/python-repl-tab-completion-on-macos/7116997#7116997
        // https://stackoverflow.com/questions/50917938/enabling-console-features-with-code-interact
        let startup_code = r#"
import code
import readline
import rlcompleter

vars = globals()
vars.update(locals())
readline.set_completer(rlcompleter.Completer(vars).complete)

if 'libedit' in readline.__doc__:
    readline.parse_and_bind("bind ^I rl_complete")
else:
    readline.parse_and_bind("tab: complete")

code.InteractiveConsole(vars).interact('Welcome to SiCl4 Python REPL!')
        "#;

        Python::with_gil(|py| {
            py.run(startup_code, None, None)
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
