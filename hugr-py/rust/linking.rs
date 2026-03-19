//! Bindings for linking utilities defined in the hugr-core crate

use pyo3::exceptions::PyException;
use pyo3::{create_exception, pymodule};

#[pymodule(submodule)]
#[pyo3(module = "hugr._hugr")]
pub mod linking {
    #[pymodule_export]
    use super::HugrLinkingError;

    use hugr_core::envelope::EnvelopeConfig;
    use hugr_core::hugr::hugrmut::HugrMut;
    use hugr_core::hugr::linking::{HugrLinking, NameLinkingPolicy};
    use hugr_core::{Hugr, HugrView};
    use pyo3::exceptions::PyValueError;
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
        let into_executable = hugr_into.entrypoint() != hugr_into.module_root();
        let from_executable = hugr_from.entrypoint() != hugr_from.module_root();
        let replacement_entrypoint = if into_executable && from_executable {
            return Err(PyValueError::new_err(
                "Cannot link two executable modules together.",
            ));
        } else if !into_executable && from_executable {
            Some(hugr_from.entrypoint())
        } else {
            None
        };

        let forest = hugr_into
            .link_module(hugr_from, &NameLinkingPolicy::default())
            .map_err(|err| HugrLinkingError::new_err(err.to_string()))?;
        if let Some(new_entrypoint) = replacement_entrypoint {
            let Some(node) = forest.node_map.get(&new_entrypoint) else {
                panic!("Entrypoint is to be replaced but was not found after linking");
            };
            hugr_into.set_entrypoint(*node);
        }
        exts_into.extend(exts_from);

        let mut result = Vec::new();
        hugr_into
            .store_with_exts(&mut result, EnvelopeConfig::binary(), &exts_into)
            .unwrap();

        // Sanity check roundtrip
        debug_assert!(hugr_core::package::Package::load(&result[..], None).is_ok());

        Ok(result)
    }
}

create_exception!(
    hugr._hugr.linking,
    HugrLinkingError,
    PyException,
    "Base exception for HUGR linking errors."
);
