//! Type-safe metadata definition for hugr nodes.
//!
//! See [HugrView::get_metadata][crate::hugr::HugrView::get_metadata] and
//! [HugrMut::set_metadata][crate::hugr::HugrMut::set_metadata] for more
//! information on how to use this API.
//!
//! # Examples
//!
//! ```
//! use hugr::hugr::{Hugr, HugrView};
//! use hugr::hugr::hugrmut::HugrMut;
//! use hugr::metadata::Metadata;
//!
//! struct SomeMetadata;
//! impl Metadata for SomeMetadata {
//!     type Type<'hugr> = &'hugr str;
//!     const KEY: &'static str = "custom.metadata";
//! }
//!
//! let mut hugr = Hugr::new();
//! hugr.set_metadata::<SomeMetadata>(hugr.module_root(), "payload");
//! let payload = hugr.get_metadata::<SomeMetadata>(hugr.module_root());
//! assert_eq!(payload, Some("payload"));
//! ```
//
// When adding new metadata keys, they should be re-exported by the python bindings.
// See hugr-py/rust/metadata.rs

/// Arbitrary metadata entry for a node.
///
/// Each entry is associated to a string key.
pub type RawMetadataValue = serde_json::Value;

/// A type-safe metadata entry
///
/// Marker structs implementing  this trait
pub trait Metadata {
    /// Key associated with the metadata entry.
    const KEY: &'static str;
    /// The type of the metadata value.
    type Type<'hugr>: serde::de::Deserialize<'hugr> + serde::ser::Serialize;
}

// -------- Core metadata entries

/// Metadata storing the name of the generator that produced the Hugr envelope.
///
/// This value is only valid when set at the module root node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HugrGenerator;
impl Metadata for HugrGenerator {
    type Type<'hugr> = crate::envelope::description::GeneratorDesc;
    const KEY: &'static str = "core.generator";
}

/// Metadata storing the list of extensions required to define the Hugr.
///
/// This list may contain additional extensions that are no longer present in
/// the Hugr.
///
/// This value is only valid when set at the module root node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HugrUsedExtensions;
impl Metadata for HugrUsedExtensions {
    type Type<'hugr> = Vec<crate::envelope::description::ExtensionDesc>;
    const KEY: &'static str = "core.used_extensions";
}
