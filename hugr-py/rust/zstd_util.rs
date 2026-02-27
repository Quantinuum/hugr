//! Zstd compression utilities for Python bindings.

use pyo3::pymodule;

#[pymodule(submodule)]
pub mod zstd {
    use pyo3::types::{PyAnyMethods, PyModule};
    use pyo3::{Bound, Python};
    use pyo3::{PyResult, exceptions::PyValueError, pyfunction};

    /// Compress data using zstd.
    ///
    /// Args:
    ///     data: The data to compress.
    ///     level: The compression level (0-22, where 0 uses the default level).
    ///
    /// Returns:
    ///     The compressed data.
    #[pyfunction]
    fn compress(data: &[u8], level: i32) -> PyResult<Vec<u8>> {
        ::zstd::encode_all(data, level).map_err(|e| PyValueError::new_err(e.to_string()))
    }

    /// Decompress zstd-compressed data.
    ///
    /// Args:
    ///     data: The compressed data.
    ///
    /// Returns:
    ///     The decompressed data.
    #[pyfunction]
    fn decompress(data: &[u8]) -> PyResult<Vec<u8>> {
        ::zstd::decode_all(data).map_err(|e| PyValueError::new_err(e.to_string()))
    }

    /// Hack: workaround for <https://github.com/PyO3/pyo3/issues/759>
    #[pymodule_init]
    fn init(m: &Bound<'_, PyModule>) -> PyResult<()> {
        Python::attach(|py| {
            py.import("sys")?
                .getattr("modules")?
                .set_item("hugr._hugr.zstd", m)
        })
    }
}
