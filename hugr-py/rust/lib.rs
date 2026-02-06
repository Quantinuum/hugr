//! Supporting Rust library for the hugr Python bindings.

mod model;
mod zstd_util;

use pyo3::pymodule;

#[pymodule]
mod _hugr {

    #[pymodule_export]
    use super::model::model;

    #[pymodule_export]
    use super::zstd_util::zstd;
}
