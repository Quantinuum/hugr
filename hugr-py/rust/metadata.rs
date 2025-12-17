//! Bindings for metadata keys defined in the hugr-core crate.

#[pyo3::pymodule]
#[pyo3(submodule)]
#[pyo3(module = "hugr._hugr.metadata")]
pub mod metadata {
    use hugr_core::metadata::Metadata;
    use pyo3::types::{PyAnyMethods, PyModule};
    use pyo3::{Bound, PyResult, Python};

    #[pymodule_export]
    const HUGR_GENERATOR: &str = hugr_core::metadata::HugrGenerator::KEY;

    #[pymodule_export]
    const HUGR_USED_EXTENSIONS: &str = hugr_core::metadata::HugrUsedExtensions::KEY;

    /// Hack: workaround for <https://github.com/PyO3/pyo3/issues/759>
    #[pymodule_init]
    fn init(m: &Bound<'_, PyModule>) -> PyResult<()> {
        Python::attach(|py| {
            py.import("sys")?
                .getattr("modules")?
                .set_item("hugr._hugr.metadata", m)
        })
    }
}
