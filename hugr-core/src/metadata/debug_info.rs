use std::any::type_name;

use crate::metadata::Metadata;
use crate::{HugrView, Node};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::{Error as JsonError, Value as JsonValue};
use thiserror::Error;

/// The HUGR metadata key for debug records
pub const DEBUGINFO_META_KEY: &str = "core.debug_info";

/// Errors related to debug info metadata
#[derive(Debug, Error)]
pub enum DebugInfoError {
    /// There is a fixed type of debug record (or None) we expect to be attached to a
    /// given HUGR node type. Any other record is rejected as invalid.
    #[error("Debug metadata does not deserialize to {0}: {1}\n{2}")]
    DRDeserializationError(&'static str, JsonError, JsonValue),
    /// After we deserialize the type, we also ensure its `kind` tag is correct.
    #[error("Debug metadata has wrong kind: got '{0}' expected '{1}'")]
    DRKindMismatchError(String, &'static str),
}

// We could remove this trait & macro if serde provided something like
// https://github.com/serde-rs/serde/pull/2908.
/// Trait which checks the "kind" string in a JSON debug record is correct
pub trait DebugRecordKind {
    fn check_kind(&self) -> Result<(), DebugInfoError>;
}

macro_rules! impl_dr_kind_check {
    ( $drtype:ty, $expected_kind:expr ) => {
        impl DebugRecordKind for $drtype {
            fn check_kind(&self) -> Result<(), DebugInfoError> {
                if &self.kind == $expected_kind {
                    Ok(())
                } else {
                    // Copy the 'kind' string because the error will outlive the (malformed) object
                    Err(DebugInfoError::DRKindMismatchError(
                        self.kind.clone(),
                        $expected_kind,
                    ))
                }
            }
        }
    };
}

/// JSON-format HUGR debug record for a compilation unit (module)
#[derive(Serialize, Deserialize)]
pub struct CompileUnitRecord {
    /// Type of the debug record (should be "compile_unit")
    pub kind: String,
    /// Working directory of the compiler
    pub directory: String,
    /// Index of the root file of the compilation unit in the file table
    pub filename: usize,
    /// Table of filenames used referenced in the debug info module
    pub file_table: Vec<String>,
}

impl Metadata for CompileUnitRecord {
    type Type<'hugr> = CompileUnitRecord;
    const KEY: &'static str = DEBUGINFO_META_KEY;
}
impl_dr_kind_check!(CompileUnitRecord, "compile_unit");

/// JSON-format HUGR debug record for a subprogram (function)
#[derive(Serialize, Deserialize)]
pub struct SubprogramRecord {
    /// Type of the debug record (should be "subprogram")
    pub kind: String,
    /// file_tab index of the file where this function is defined
    pub file: usize,
    /// Line number where this function's declaration begins
    pub line_no: usize,
    // TODO: waiting on scopes in milestone 2
    //scope: Option<ScopeRecord>,
    /// Line number where this function's body begins
    pub scope_line: usize,
}

impl Metadata for SubprogramRecord {
    type Type<'hugr> = SubprogramRecord;
    const KEY: &'static str = DEBUGINFO_META_KEY;
}
impl_dr_kind_check!(SubprogramRecord, "subprogram");

/// JSON-format HUGR debug record for a source code location
#[derive(Serialize, Deserialize)]
pub struct LocationRecord {
    /// Type of the debug record (should be "location")
    pub kind: String,
    /// Column number of the location
    pub column: usize,
    /// Line number of the location
    pub line_no: usize,
}

impl Metadata for LocationRecord {
    type Type<'hugr> = LocationRecord;
    const KEY: &'static str = DEBUGINFO_META_KEY;
}
impl_dr_kind_check!(LocationRecord, "location");

/// Inspect the debug metadata attached to the HUGR node.
///
/// If there is no debug metadata, return Ok(None). If it is present but is not a valid
/// `T`, return a DebugInfoError. Otherwise, return the deserialized record as Ok(Some(`T`)).
pub fn try_get_debug_meta<
    'h,
    H: HugrView<Node = Node>,
    T: Metadata<Type<'h> = T> + DeserializeOwned + DebugRecordKind + 'h,
>(
    hugr: &'h H,
    node: Node,
) -> Result<Option<T>, DebugInfoError> {
    if let Some(json) = hugr.get_metadata_any(node, DEBUGINFO_META_KEY) {
        let debug_record = serde_json::from_value::<T>(json.clone()).map_err(|e| {
            DebugInfoError::DRDeserializationError(type_name::<T>(), e, json.clone())
        })?;
        debug_record.check_kind()?;
        Ok(Some(debug_record))
    } else {
        Ok(None)
    }
}
