//! Bindings for linking utilities defined in the hugr-core crate

use hugr_core::hugr::hugrmut::HugrMut;
use hugr_core::hugr::linking::{HugrLinking, NameLinkingPolicy};
use hugr_core::{Hugr, HugrView};
use pyo3::exceptions::PyException;
use pyo3::{create_exception, pymodule};

#[derive(derive_more::Display, Debug)]
enum LinkError {
    #[display("Could not link modules: {_0}")]
    LinkError(String),
    #[display("Cannot link two modules with non-root entrypoints together.")]
    BothNonRootEntrypoint,
}

fn link(hugr_into: &mut Hugr, hugr_from: Hugr) -> Result<(), LinkError> {
    let into_non_root_entrypoint = hugr_into.entrypoint() != hugr_into.module_root();
    let from_non_root_entrypoint = hugr_from.entrypoint() != hugr_from.module_root();
    let replacement_entrypoint = if into_non_root_entrypoint && from_non_root_entrypoint {
        return Err(LinkError::BothNonRootEntrypoint);
    } else if !into_non_root_entrypoint && from_non_root_entrypoint {
        Some(hugr_from.entrypoint())
    } else {
        None
    };

    let forest = hugr_into
        .link_module(hugr_from, &NameLinkingPolicy::default())
        .map_err(|err| LinkError::LinkError(err.to_string()))?;
    if let Some(new_entrypoint) = replacement_entrypoint {
        let Some(node) = forest.node_map.get(&new_entrypoint) else {
            panic!("Entrypoint is to be replaced but was not found after linking");
        };
        hugr_into.set_entrypoint(*node);
    }

    Ok(())
}

#[pymodule(submodule)]
#[pyo3(module = "hugr._hugr")]
pub mod linking {
    #[pymodule_export]
    use super::HugrLinkingError;

    use hugr_core::Hugr;
    use hugr_core::envelope::EnvelopeConfig;
    use hugr_core::extension::ExtensionRegistry;
    use hugr_core::package::Package;
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
                PyValueError::new_err(format!("Loading of first envelope failed: {err}"))
            })?;
        let (hugr_from, exts_from) = Hugr::load_with_exts(module_from, None).map_err(|err| {
            PyValueError::new_err(format!("Loading of second envelope failed: {err}"))
        })?;

        super::link(&mut hugr_into, hugr_from)
            .map_err(|err| HugrLinkingError::new_err(err.to_string()))?;
        exts_into.extend(exts_from);

        let mut result = Vec::new();
        hugr_into
            .store_with_exts(&mut result, EnvelopeConfig::binary(), &exts_into)
            .unwrap();

        // Sanity check roundtrip
        debug_assert!(Package::load(&result[..], None).is_ok());

        Ok(result)
    }

    #[pyfunction]
    fn link_packages(packages: Vec<Vec<u8>>) -> PyResult<Vec<u8>> {
        let loaded_packages: Result<Vec<_>, _> = packages
            .into_iter()
            .enumerate()
            .map(|(i, pkg_bytes)| {
                Package::load(pkg_bytes.as_slice(), None).map_err(|err| {
                    PyValueError::new_err(format!("Loading of envelope {i} failed: {err}"))
                })
            })
            .collect();
        let (modules, extensions): (Vec<_>, Vec<_>) = loaded_packages?
            .into_iter()
            .map(|pkg| (pkg.modules, pkg.extensions))
            .unzip();
        let mut modules = modules.into_iter().flatten();

        let mut result_pkg = Package {
            modules: Vec::new(),
            extensions: extensions.into_iter().fold(
                ExtensionRegistry::default(),
                |mut into, from| {
                    into.extend(from);
                    into
                },
            ),
        };
        if let Some(mut first_module) = modules.next() {
            for (i, next_module) in modules.enumerate() {
                super::link(&mut first_module, next_module).map_err(|err| {
                    HugrLinkingError::new_err(format!("Could not link module {}: {err}", i + 1))
                })?;
            }
            result_pkg.modules.push(first_module);
        };

        let mut result = Vec::new();
        result_pkg
            .store(&mut result, EnvelopeConfig::binary())
            .unwrap();

        // Sanity check roundtrip
        debug_assert!(Package::load(&result[..], None).is_ok());

        Ok(result)
    }
}

create_exception!(
    hugr._hugr.linking,
    HugrLinkingError,
    PyException,
    "Base exception for HUGR linking errors."
);
