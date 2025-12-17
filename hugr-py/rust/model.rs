//! Bindings for hugr-model crate.

use hugr_cli::RunWithIoError;

use pyo3::exceptions::{PyException, PyValueError};
use pyo3::{PyErr, PyResult, create_exception, pymodule};

#[pymodule]
pub mod model {
    use hugr_cli::CliArgs;
    use hugr_model::v0::ast;
    use pyo3::exceptions::PyValueError;
    use pyo3::{PyResult, pyfunction};

    #[pymodule_export]
    use super::HugrCliDescribeError;
    #[pymodule_export]
    use super::HugrCliError;

    #[pymodule_export]
    use super::string_to_term;
    #[pymodule_export]
    use super::term_to_string;

    #[pymodule_export]
    use super::node_to_string;
    #[pymodule_export]
    use super::string_to_node;

    #[pymodule_export]
    use super::region_to_string;
    #[pymodule_export]
    use super::string_to_region;

    #[pymodule_export]
    use super::module_to_string;
    #[pymodule_export]
    use super::string_to_module;

    #[pymodule_export]
    use super::param_to_string;
    #[pymodule_export]
    use super::string_to_param;

    #[pymodule_export]
    use super::string_to_symbol;
    #[pymodule_export]
    use super::symbol_to_string;

    #[pymodule_export]
    use super::package_to_string;
    #[pymodule_export]
    use super::string_to_package;

    #[pyfunction]
    fn package_to_bytes(package: ast::Package) -> PyResult<Vec<u8>> {
        let bump = bumpalo::Bump::new();
        let resolved = package
            .resolve(&bump)
            .map_err(|err| PyValueError::new_err(err.to_string()))?;
        let bytes = hugr_model::v0::binary::write_to_vec(&resolved);
        Ok(bytes)
    }

    #[pyfunction]
    fn bytes_to_package(bytes: &[u8]) -> PyResult<(ast::Package, Vec<u8>)> {
        let bump = bumpalo::Bump::new();
        let (table, suffix) = hugr_model::v0::binary::read_from_slice_with_suffix(bytes, &bump)
            .map_err(|err| PyValueError::new_err(err.to_string()))?;
        let package = table
            .as_ast()
            .ok_or_else(|| PyValueError::new_err("Malformed package"))?;
        Ok((package, suffix))
    }

    /// Returns the current version of the HUGR model format as a tuple of (major, minor, patch).
    #[pyfunction]
    fn current_model_version() -> (u64, u64, u64) {
        (
            hugr_model::CURRENT_VERSION.major,
            hugr_model::CURRENT_VERSION.minor,
            hugr_model::CURRENT_VERSION.patch,
        )
    }

    /// Directly invoke the HUGR CLI entrypoint.
    /// Arguments are extracted from std::env::args().
    #[pyfunction]
    fn run_cli() {
        // python is the first arg so skip it
        CliArgs::new_from_args(std::env::args().skip(1)).run_cli();
    }

    /// Run a CLI command with bytes input and return bytes output.
    ///
    /// This function provides a programmatic interface to the HUGR CLI,
    /// allowing Python code to pass input data as bytes and receive output
    /// as bytes, without needing to use stdin/stdout or temporary files.
    ///
    /// # Arguments
    ///
    /// * `args` - Command line arguments as a list of strings, not including the executable name.
    /// * `input_bytes` - Optional input data as bytes (e.g., a HUGR package)
    ///
    /// # Returns
    ///
    /// Returns the command output as bytes, maybe empty.
    /// Raises an exception on error.
    ///
    /// Errors or tracing may still be printed to stderr as normal.
    #[pyfunction]
    #[pyo3(signature = (args, input_bytes=None))]
    fn cli_with_io(mut args: Vec<String>, input_bytes: Option<&[u8]>) -> PyResult<Vec<u8>> {
        // placeholder for executable
        args.insert(0, String::new());
        let cli_args = CliArgs::new_from_args(args);
        let input = input_bytes.unwrap_or(&[]);
        cli_args.run_with_io(input).map_err(super::cli_error_to_py)
    }
}

// Define custom exceptions
create_exception!(
    _hugr,
    HugrCliError,
    PyException,
    "Base exception for HUGR CLI errors."
);
create_exception!(
    _hugr,
    HugrCliDescribeError,
    HugrCliError,
    "Exception for HUGR CLI describe command errors with partial output."
);

macro_rules! syntax_to_and_from_string {
    ($name:ident, $ty:ty) => {
        pastey::paste! {
            #[pyo3::pyfunction]
            fn [<$name _to_string>](ob: hugr_model::v0::ast::$ty) -> PyResult<String> {
                Ok(format!("{}", ob))
            }

            #[pyo3::pyfunction]
            fn [<string_to_ $name>](string: String) -> PyResult<hugr_model::v0::ast::$ty> {
                string
                    .parse::<hugr_model::v0::ast::$ty>()
                    .map_err(|err| PyValueError::new_err(err.to_string()))
            }
        }
    };
}
syntax_to_and_from_string!(term, Term);
syntax_to_and_from_string!(node, Node);
syntax_to_and_from_string!(region, Region);
syntax_to_and_from_string!(module, Module);
syntax_to_and_from_string!(param, Param);
syntax_to_and_from_string!(symbol, Symbol);
syntax_to_and_from_string!(package, Package);

/// Helper to convert RunWithIoError to Python exception
fn cli_error_to_py(err: RunWithIoError) -> PyErr {
    match err {
        RunWithIoError::Describe { source, output } => {
            // Convert output bytes to string, falling back to empty string if invalid UTF-8
            let output_str = String::from_utf8(output).unwrap_or_else(|e| {
                format!("<Invalid UTF-8 output: {} bytes>", e.as_bytes().len())
            });

            HugrCliDescribeError::new_err((format!("{:?}", source), output_str))
        }
        RunWithIoError::Other(e) => HugrCliError::new_err(format!("{:?}", e)),
        _ => {
            // Catch-all for any future error variants (non_exhaustive enum)
            HugrCliError::new_err(format!("{:?}", err))
        }
    }
}
