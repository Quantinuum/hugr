//! Supporting Rust library for the hugr Python bindings.

mod model;

use pyo3::pymodule;

#[pymodule]
mod _hugr {

    #[pymodule_export]
    use super::model::model;
}
