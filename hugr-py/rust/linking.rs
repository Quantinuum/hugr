//! Bindings for linking utilities defined in the hugr-core crate

use pyo3::pymodule;

#[pymodule(submodule)]
#[pyo3(module = "hugr._hugr.linking")]
pub mod linking {
    use hugr_core;
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
        let mut pkg_into = hugr_core::package::Package::load(module_into, None).map_err(|err| {
            PyValueError::new_err(format!("Loading of first envelope failed: {}", err))
        })?; // TODO need a combination of loading a package, and expecting a single hugr in it.

        let pkg_from = hugr_core::package::Package::load(module_from, None).map_err(|err| {
            PyValueError::new_err(format!("Loading of second envelope failed: {}", err))
        })?;

        pkg_into.modules[0]
            .link_module(
                pkg_from.modules.into_iter().next().unwrap(),
                &NameLinkingPolicy::default(),
            )
            .map_err(|err| PyRuntimeError::new_err(err.to_string()))?; // TODO Add a proper error

        pkg_into.extensions.extend(pkg_from.extensions);

        let mut result = Vec::new();
        pkg_into
            .store(&mut result, EnvelopeConfig::binary())
            .unwrap();

        hugr_core::package::Package::load(&result[..], None)
            .map_err(|err| PyValueError::new_err(format!("Roundtrip failed: {:?}", err)))?;

        Ok(result)
    }
}
