#![allow(missing_docs)]

use crate::metadata::Metadata;
use crate::{HugrView, Node};
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub const DEBUGINFO_META_KEY: &str = "core.debug_info";

#[derive(Serialize, Deserialize)]
pub struct CompileUnitRecord {
    pub directory: String,
    pub filename: usize,
    pub file_table: Vec<String>,
}

impl Metadata for CompileUnitRecord {
    type Type<'hugr> = CompileUnitRecord;
    const KEY: &'static str = DEBUGINFO_META_KEY;
}

#[derive(Debug, Error)]
pub enum DebugInfoError {
    /// There is a specific required mapping between HUGR nodes and debug record types,
    /// if present
    #[error("Debug info does not match expected type")]
    DRTypeMismatchError,
}

#[derive(Serialize, Deserialize)]
pub struct SubprogramRecord {
    pub file: usize,
    pub line_no: usize,
    // TODO
    //scope: Option<ScopeRecord>,
    pub scope_line: usize,
}

impl Metadata for SubprogramRecord {
    type Type<'hugr> = SubprogramRecord;
    const KEY: &'static str = DEBUGINFO_META_KEY;
}

#[derive(Serialize, Deserialize)]
pub struct LocationRecord {
    pub column: usize,
    pub line_no: usize,
}

impl Metadata for LocationRecord {
    type Type<'hugr> = LocationRecord;
    const KEY: &'static str = DEBUGINFO_META_KEY;
}

// TODO: could generalize this to all metadata
/// Inspect the debug metadata attached to the HUGR node.
///
/// If there is no debug metadata, return Ok(None). If it is present but does not
/// deserialize into `T`, return DRTypeMismatchError. Otherwise, return the deserialized
/// Some(`T`).
pub fn try_get_debug_meta<'h, H: HugrView<Node = Node>, T: Metadata<Type<'h> = T>>(
    hugr: &'h H,
    node: Node,
) -> Result<Option<T>, DebugInfoError> {
    if hugr.get_metadata_any(node, DEBUGINFO_META_KEY).is_some() {
        if let Some(record) = hugr.get_metadata::<T>(node) {
            Ok(Some(record))
        } else {
            Err(DebugInfoError::DRTypeMismatchError)
        }
    } else {
        Ok(None)
    }
}
