use std::any::type_name;
use std::fmt;

use crate::metadata::Metadata;
use crate::{HugrView, Node};
use serde::{
    Deserialize, Serialize,
    de::{DeserializeOwned, Deserializer, Error as DeError, Visitor},
};
use serde_json::{Error as JsonError, Value as JsonValue};
use thiserror::Error;

/// The HUGR metadata key for debug records
pub const DEBUGINFO_META_KEY: &str = "core.debug_info";

/// Visitor and wrapper function passed as "deserialize_with" attribute
/// which try to deserialize a usize from either a string or number
struct JsonStrToIntVisitor;

impl<'de> Visitor<'de> for JsonStrToIntVisitor {
    type Value = usize;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a usize or a string convertible with str::parse<usize>()")
    }

    fn visit_str<E: DeError>(self, s: &str) -> Result<Self::Value, E> {
        s.parse::<usize>().map_err(E::custom)
    }

    fn visit_u64<E: DeError>(self, x: u64) -> Result<Self::Value, E> {
        x.try_into().map_err(E::custom)
    }
}

fn deserialize_usize_str<'de, D: Deserializer<'de>>(deserializer: D) -> Result<usize, D::Error> {
    deserializer.deserialize_any(JsonStrToIntVisitor)
}

/// JSON-format HUGR debug record for a compilation unit (module)
#[derive(Serialize, Deserialize)]
pub struct CompileUnitRecord {
    /// Working directory of the compiler
    pub directory: String,
    /// Index of the root file of the compilation unit in the file table
    #[serde(deserialize_with = "deserialize_usize_str")]
    pub filename: usize,
    /// Table of filenames used referenced in the debug info module
    pub file_table: Vec<String>,
}

impl Metadata for CompileUnitRecord {
    type Type<'hugr> = CompileUnitRecord;
    const KEY: &'static str = DEBUGINFO_META_KEY;
}

/// Errors related to debug info metadata
#[derive(Debug, Error)]
pub enum DebugInfoError {
    /// There is a specific required mapping between HUGR nodes and debug record types,
    /// if present
    #[error("Debug metadata does not deserialize to {0}: {1}\n{2}")]
    DRTypeMismatchError(&'static str, JsonError, JsonValue),
}

/// JSON-format HUGR debug record for a subprogram (function)
#[derive(Serialize, Deserialize)]
pub struct SubprogramRecord {
    /// file_tab index of the file where this function is defined
    #[serde(deserialize_with = "deserialize_usize_str")]
    pub file: usize,
    /// Line number where this function's declaration begins
    #[serde(deserialize_with = "deserialize_usize_str")]
    pub line_no: usize,
    // TODO: waiting on scopes in milestone 2
    //scope: Option<ScopeRecord>,
    /// Line number where this function's body begins
    #[serde(deserialize_with = "deserialize_usize_str")]
    pub scope_line: usize,
}

impl Metadata for SubprogramRecord {
    type Type<'hugr> = SubprogramRecord;
    const KEY: &'static str = DEBUGINFO_META_KEY;
}

/// JSON-format HUGR debug record for a source code location
#[derive(Serialize, Deserialize)]
pub struct LocationRecord {
    /// Column number of the location
    #[serde(deserialize_with = "deserialize_usize_str")]
    pub column: usize,
    /// Line number of the location
    #[serde(deserialize_with = "deserialize_usize_str")]
    pub line_no: usize,
}

impl Metadata for LocationRecord {
    type Type<'hugr> = LocationRecord;
    const KEY: &'static str = DEBUGINFO_META_KEY;
}

/// Inspect the debug metadata attached to the HUGR node.
///
/// If there is no debug metadata, return Ok(None). If it is present but does not
/// deserialize into `T`, return DRTypeMismatchError. Otherwise, return the deserialized
/// Some(`T`).
pub fn try_get_debug_meta<
    'h,
    H: HugrView<Node = Node>,
    T: Metadata<Type<'h> = T> + DeserializeOwned,
>(
    hugr: &'h H,
    node: Node,
) -> Result<Option<T>, DebugInfoError> {
    if let Some(json) = hugr.get_metadata_any(node, DEBUGINFO_META_KEY) {
        serde_json::from_value::<T>(json.clone())
            .map_err(|e| DebugInfoError::DRTypeMismatchError(type_name::<T>(), e, json.clone()))
            .map(|debug_record| Some(debug_record))
    } else {
        Ok(None)
    }
}
