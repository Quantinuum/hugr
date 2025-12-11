//! Type-safe metadata definition for hugr nodes.

/// Arbitrary metadata entry for a node.
///
/// Each entry is associated to a string key.
pub type RawMetadataValue = serde_json::Value;

/// A type-safe metadata entry
///
/// Marker structs implementing  this trait
pub trait Metadata {
    type Type<'hugr>: serde::de::Deserialize<'hugr> + serde::ser::Serialize;
    const KEY: &'static str;
}
