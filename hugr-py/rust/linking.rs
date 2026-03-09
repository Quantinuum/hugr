//! Bindings for linking utilities defined in the hugr-core crate

use pyo3::pymodule;

#[pymodule(submodule)]
#[pyo3(module = "hugr._hugr.linking")]
pub mod linking {
    /// Hack: workaround for <https://github.com/PyO3/pyo3/issues/759>
    #[pymodule_init]
    fn init(m: &Bound<'_, PyModule>) -> PyResult<()> {
        Python::attach(|py| {
            py.import("sys")?
                .getattr("modules")?
                .set_item("hugr._hugr.linking", m)
        })
    }

    use hugr_core;
    use hugr_core::envelope::EnvelopeConfig;
    use hugr_core::hugr::linking::{HugrLinking, NameLinkingPolicy};
    use hugr_core::std_extensions::std_reg;
    use pyo3::exceptions::{PyRuntimeError, PyValueError};
    use pyo3::types::{PyAnyMethods, PyModule};
    use pyo3::{Bound, PyResult, Python, pyfunction};

    #[pyfunction]
    fn link_modules(module_into: Option<&[u8]>, module_from: Option<&[u8]>) -> PyResult<Vec<u8>> {
        let reg = std_reg();
        let mut hugr_into = hugr_core::Hugr::load(module_into.unwrap(), Some(&reg))
            .map_err(|err| PyValueError::new_err(err.to_string()))?;
        let hugr_from = hugr_core::Hugr::load(module_from.unwrap(), Some(&reg))
            .map_err(|err| PyValueError::new_err(err.to_string()))?;

        hugr_into
            .link_module(hugr_from, &NameLinkingPolicy::default())
            .map_err(|err| PyRuntimeError::new_err(err.to_string()))?; // TODO Add a proper error

        let mut result = Vec::new();
        hugr_into
            .store(&mut result, EnvelopeConfig::default())
            .map_err(|err| PyRuntimeError::new_err(err.to_string()))?; // TODO Add a proper error
        Ok(result)
    }
}
