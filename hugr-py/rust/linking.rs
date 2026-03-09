//! Bindings for linking utilities defined in the hugr-core crate

use pyo3::pymodule;

#[pymodule(submodule)]
#[pyo3(module = "hugr._hugr.linking")]
pub mod linking {
    use hugr_core::Hugr;
    use hugr_core::envelope::EnvelopeConfig;
    use hugr_core::hugr::linking::{HugrLinking, NameLinkingPolicy};
    use pyo3::exceptions::{PyRuntimeError, PyValueError};
    use pyo3::types::{PyAnyMethods, PyModule};
    use pyo3::{Bound, PyResult, Python, pyfunction};

    /// Hack: workaround for <https://github.com/PyO3/pyo3/issues/759>
    #[pymodule_init]
    fn init(m: &Bound<'_, PyModule>) -> PyResult<()> {
        Python::attach(|py| {
            py.import("sys")?
                .getattr("modules")?
                .set_item("hugr._hugr.linking", m)
        })
    }

    #[pyfunction]
    fn link_modules(module_into: &[u8], module_from: &[u8]) -> PyResult<Vec<u8>> {
        let (mut hugr_into, mut exts_into) =
            Hugr::load_with_exts(module_into, None).map_err(|err| {
                PyValueError::new_err(format!("Loading of first envelope failed: {}", err))
            })?;

        let (hugr_from, exts_from) = Hugr::load_with_exts(module_from, None).map_err(|err| {
            PyValueError::new_err(format!("Loading of second envelope failed: {}", err))
        })?;

        hugr_into
            .link_module(hugr_from, &NameLinkingPolicy::default())
            .map_err(|err| PyRuntimeError::new_err(err.to_string()))?; // TODO Add a proper error

        exts_into.extend(exts_from);

        let mut result = Vec::new();
        hugr_into
            .store_with_exts(&mut result, EnvelopeConfig::binary(), &exts_into)
            .unwrap();

        hugr_core::package::Package::load(&result[..], None)
            .map_err(|err| PyValueError::new_err(format!("Roundtrip failed: {:?}", err)))?;

        Ok(result)
    }
}
