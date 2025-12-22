//! Supporting Rust library for the hugr Python bindings.

mod metadata;
mod model;

use pyo3::pymodule;

#[pymodule]
mod _hugr {
    #[pymodule_export]
    use super::metadata::metadata;
    #[pymodule_export]
    use super::model::model;
}
