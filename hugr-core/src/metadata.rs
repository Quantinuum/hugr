//! Type-safe metadata definition for hugr nodes.

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
/// This list may contain additional extensions that are not longer present in
/// the Hugr.
///
/// This value is only valid when set at the module root node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HugrUsedExtensions;
impl Metadata for HugrUsedExtensions {
    type Type<'hugr> = Vec<crate::envelope::description::ExtensionDesc>;
    const KEY: &'static str = "core.used_extensions";
}
