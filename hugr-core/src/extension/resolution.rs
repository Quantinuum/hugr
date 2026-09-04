//! Utilities for resolving operations and types present in a HUGR, and updating
//! the list of used extensions.
//!
//! The functionalities of this module can be called from the type methods
//! [`crate::ops::OpType::used_extensions`] and
//! [`crate::types::Signature::used_extensions`].
//!
//! When listing "used extensions" we only care about _definitional_ extension
//! requirements, i.e., the operations and types that are required to define the
//! HUGR nodes and wire types. This is computed from the union of all extension
//! required across the HUGR.
//!
//! Note: These procedures are only temporary until `hugr-model` is stabilized.
//! Once that happens, hugrs will no longer be directly deserialized using serde
//! but instead will be created by the methods in `crate::import`. As these
//! (will) automatically resolve extensions as the operations are created, we
//! will no longer require this post-facto resolution step.

mod extension;
mod ops;
mod types;
mod types_mut;
mod weak_registry;

pub use weak_registry::WeakExtensionRegistry;

pub(crate) use ops::{collect_op_extension, resolve_op_extensions};
pub(crate) use types::{collect_op_types_extensions, collect_signature_exts, collect_term_exts};
pub(crate) use types_mut::TypeExtensionResolver;

use derive_more::{Display, Error, From};
use itertools::Itertools;

use super::{Extension, ExtensionId, ExtensionRegistry, ExtensionSet, Version, semver_compatible};
use crate::Node;
use crate::core::HugrNode;
use crate::ops::constant::ValueName;
use crate::ops::custom::OpaqueOpError;
use crate::ops::{NamedOp, OpName, OpType, Value};
use crate::types::{CustomType, Signature, Type, TypeArg, TypeName};

/// Update all weak Extension pointers inside a type.
pub fn resolve_type_extensions(
    typ: &mut Type,
    extensions: &WeakExtensionRegistry,
) -> Result<(), ExtensionResolutionError> {
    TypeExtensionResolver::new(extensions).resolve_type(None, typ)
}

/// Update all weak Extension pointers in a custom type.
pub fn resolve_custom_type_extensions(
    typ: &mut CustomType,
    extensions: &WeakExtensionRegistry,
) -> Result<(), ExtensionResolutionError> {
    TypeExtensionResolver::new(extensions).resolve_custom_type(None, typ)
}

/// Update all weak Extension pointers inside a type argument.
pub fn resolve_typearg_extensions(
    arg: &mut TypeArg,
    extensions: &WeakExtensionRegistry,
) -> Result<(), ExtensionResolutionError> {
    TypeExtensionResolver::new(extensions).resolve_term(None, arg)
}

/// Update all weak Extension pointers inside a constant value.
pub fn resolve_value_extensions(
    value: &mut Value,
    extensions: &WeakExtensionRegistry,
) -> Result<(), ExtensionResolutionError> {
    TypeExtensionResolver::new(extensions).resolve_value(None, value)
}

/// Errors that can occur during extension resolution.
#[derive(Debug, Display, Clone, Error, From, PartialEq)]
#[non_exhaustive]
pub enum ExtensionResolutionError<N: HugrNode = Node> {
    /// Could not resolve an opaque operation to an extension operation.
    #[display("Error resolving opaque operation: {_0}")]
    #[from]
    OpaqueOpError(OpaqueOpError<N>),
    /// A legacy unversioned operation requires an extension that is not in the registry.
    #[deprecated(since = "0.30.2", note = "use `UnresolvedOpExtension` instead")]
    #[display(
        "{op}{} requires extension {missing_extension}, but it could not be found in the extension list used during resolution. The available extensions are: {}",
        node.map(|n| format!(" in {n}")).unwrap_or_default(),
        available_extensions.join(", ")
    )]
    MissingOpExtension {
        /// The node that requires the extension.
        node: Option<N>,
        /// The operation that requires the extension.
        op: OpName,
        /// The missing extension
        missing_extension: ExtensionId,
        /// A list of available extensions.
        available_extensions: Vec<ExtensionId>,
    },
    /// A legacy unversioned type references an extension that is not in the registry.
    #[deprecated(since = "0.30.2", note = "use `UnresolvedTypeExtension` instead")]
    #[display(
        "Type {ty}{} requires extension {missing_extension}, but it could not be found in the extension list used during resolution. The available extensions are: {}",
        node.map(|n| format!(" in {n}")).unwrap_or_default(),
        available_extensions.join(", ")
    )]
    MissingTypeExtension {
        /// The node that requires the extension.
        node: Option<N>,
        /// The type that requires the extension.
        ty: TypeName,
        /// The missing extension
        missing_extension: ExtensionId,
        /// A list of available extensions.
        available_extensions: Vec<ExtensionId>,
    },
    /// A type definition's `extension_id` does not match the extension it is in.
    #[display(
        "Type definition {def} in extension {extension} declares it was defined in {wrong_extension} instead."
    )]
    WrongTypeDefExtension {
        /// The extension that defines the type.
        extension: ExtensionId,
        /// The type definition name.
        def: TypeName,
        /// The extension declared in the type definition's `extension_id`.
        wrong_extension: ExtensionId,
    },
    /// An operation definition's `extension_id` does not match the extension it is in.
    #[display(
        "Operation definition {def} in extension {extension} declares it was defined in {wrong_extension} instead."
    )]
    WrongOpDefExtension {
        /// The extension that defines the op.
        extension: ExtensionId,
        /// The op definition name.
        def: OpName,
        /// The extension declared in the op definition's `extension_id`.
        wrong_extension: ExtensionId,
    },
    /// The type of an `OpaqueValue` has types which do not reference their defining extensions.
    #[display(
        "The type of the opaque value '{value}' requires extensions {missing_extensions}, but does not reference their definition."
    )]
    InvalidConstTypes {
        /// The value that has invalid types.
        value: ValueName,
        /// The missing extension.
        missing_extensions: ExtensionSet,
    },
    /// Error while collecting extension dependencies.
    #[display("Error collecting extension dependencies: {_0}")]
    #[from]
    ExtensionDependencyError(ExtensionCollectionError<N>),
    /// A versioned extension required by an operation could not be resolved.
    #[display(
        "Could not resolve operation {op}{}: {}",
        node.map(|n| format!(" in {n}")).unwrap_or_default(),
        description.failure()
    )]
    UnresolvedOpExtension {
        /// The node that requires the extension.
        node: Option<N>,
        /// The operation that requires the extension.
        op: OpName,
        /// The required and available extension versions.
        description: Box<ExtensionResolutionErrorDescription>,
    },
    /// A versioned extension required by a type could not be resolved.
    #[display(
        "Could not resolve type {ty}{}: {}",
        node.map(|n| format!(" in {n}")).unwrap_or_default(),
        description.failure()
    )]
    UnresolvedTypeExtension {
        /// The node that requires the extension.
        node: Option<N>,
        /// The type that requires the extension.
        ty: TypeName,
        /// The required and available extension versions.
        description: Box<ExtensionResolutionErrorDescription>,
    },
}

impl<N: HugrNode> ExtensionResolutionError<N> {
    /// Create an error for a missing legacy unversioned operation extension.
    #[deprecated(since = "0.30.2", note = "use `unresolved_op_extension` instead")]
    #[expect(deprecated)]
    pub fn missing_op_extension(
        node: Option<N>,
        op: &OpType,
        missing_extension: &ExtensionId,
        extensions: &ExtensionRegistry,
    ) -> Self {
        Self::MissingOpExtension {
            node,
            op: NamedOp::name(op),
            missing_extension: missing_extension.clone(),
            available_extensions: extensions.ids().cloned().collect(),
        }
    }

    /// Create an error for a missing legacy unversioned type extension.
    #[deprecated(since = "0.30.2", note = "use `unresolved_type_extension` instead")]
    #[expect(deprecated)]
    pub fn missing_type_extension(
        node: Option<N>,
        ty: &TypeName,
        missing_extension: &ExtensionId,
        extensions: &WeakExtensionRegistry,
    ) -> Self {
        Self::MissingTypeExtension {
            node,
            ty: ty.clone(),
            missing_extension: missing_extension.clone(),
            available_extensions: extensions.ids().cloned().collect(),
        }
    }

    /// Create an error for a failed versioned operation extension lookup.
    pub fn unresolved_op_extension(
        node: Option<N>,
        op: OpName,
        required_extension: &ExtensionId,
        required_version: &Version,
        extensions: &ExtensionRegistry,
    ) -> Self {
        let description = Box::new(ExtensionResolutionErrorDescription::from_registry(
            required_extension,
            required_version,
            extensions,
        ));
        Self::UnresolvedOpExtension {
            node,
            op,
            description,
        }
    }

    /// Create an error for a failed versioned type extension lookup.
    pub fn unresolved_type_extension(
        node: Option<N>,
        ty: &TypeName,
        required_extension: &ExtensionId,
        required_version: &Version,
        extensions: &WeakExtensionRegistry,
    ) -> Self {
        let description = Box::new(ExtensionResolutionErrorDescription::from_weak_registry(
            required_extension,
            required_version,
            extensions,
        ));
        Self::UnresolvedTypeExtension {
            node,
            ty: ty.clone(),
            description,
        }
    }
}

/// Version information for an extension that could not be resolved.
///
/// The available extensions are stored in registry order so diagnostics are
/// deterministic. Each entry includes both its id and version, allowing the
/// description to be shared by missing-extension and version-mismatch errors.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExtensionResolutionErrorDescription {
    /// The required extension id.
    pub required_extension: ExtensionId,
    /// The minimum compatible extension version required by the HUGR.
    pub required_version: Version,
    /// The extension versions available during resolution.
    pub available_extensions: Vec<(ExtensionId, Version)>,
}

impl ExtensionResolutionErrorDescription {
    /// Describe a failed lookup in a strong extension registry.
    fn from_registry(
        required_extension: &ExtensionId,
        required_version: &Version,
        extensions: &ExtensionRegistry,
    ) -> Self {
        Self {
            required_extension: required_extension.clone(),
            required_version: required_version.clone(),
            available_extensions: extensions
                .iter_all()
                .map(|extension| (extension.name().clone(), extension.version().clone()))
                .collect(),
        }
    }

    /// Describe a failed lookup in a weak extension registry.
    fn from_weak_registry(
        required_extension: &ExtensionId,
        required_version: &Version,
        extensions: &WeakExtensionRegistry,
    ) -> Self {
        Self {
            required_extension: required_extension.clone(),
            required_version: required_version.clone(),
            available_extensions: extensions
                .iter_all()
                .map(|(id, version, _)| (id.clone(), version.clone()))
                .collect(),
        }
    }

    /// Format the required extension as `id@version`.
    fn required(&self) -> String {
        format!("{}@{}", self.required_extension, self.required_version)
    }

    /// Format every available extension as `id@version`.
    fn available(&self) -> String {
        self.available_extensions
            .iter()
            .map(|(id, version)| format!("{id}@{version}"))
            .join(", ")
    }

    /// Explain why the extension requirement could not be resolved.
    ///
    /// If the extension id is absent, the complete registry contents are
    /// included. A lower version in the same compatibility group means that
    /// the requirement is newer than the registry entry. Otherwise, all
    /// versions registered under the requested extension id are incompatible.
    fn failure(&self) -> String {
        let available_versions: Vec<_> = self
            .available_extensions
            .iter()
            .filter_map(|(id, version)| (id == &self.required_extension).then_some(version))
            .collect();
        if available_versions.is_empty() {
            return format!(
                "Extension {} is required, but it was not found. The available extensions are: {}",
                self.required(),
                self.available()
            );
        }
        if let Some(version) = available_versions
            .iter()
            .copied()
            .filter(|version| {
                *version < &self.required_version
                    && semver_compatible(&self.required_version, version)
            })
            .max()
        {
            return format!(
                "Extension {} is required, but the available version {version} is too old",
                self.required()
            );
        }

        format!(
            "Extension {} is required, but the available versions [{}] are incompatible",
            self.required(),
            available_versions.iter().join(", ")
        )
    }
}

/// Errors that can occur when collecting extension requirements.
#[derive(Debug, Display, Clone, Error, PartialEq)]
#[non_exhaustive]
pub enum ExtensionCollectionError<N: HugrNode = Node> {
    /// An operation requires an extension that is not in the given registry.
    #[display(
        "{op}{} contains custom types which have lost the reference to their defining extensions. Dropped extensions: {}",
        if let Some(node) = node { format!(" ({node})") } else { String::new() },
        missing_extensions.join(", ")
    )]
    DroppedOpExtensions {
        /// The node that is missing extensions.
        node: Option<N>,
        /// The operation that is missing extensions.
        op: OpName,
        /// The missing extensions.
        missing_extensions: Vec<ExtensionId>,
    },
    /// A signature requires an extension that is not in the given registry.
    #[display(
        "Signature {signature} contains custom types which have lost the reference to their defining extensions. Dropped extensions: {}",
        missing_extensions.join(", ")
    )]
    DroppedSignatureExtensions {
        /// The signature that is missing extensions.
        signature: String,
        /// The missing extensions.
        missing_extensions: Vec<ExtensionId>,
    },
    /// A signature requires an extension that is not in the given registry.
    #[display(
        "Type {typ} contains custom types which have lost the reference to their defining extensions. Dropped extensions: {}",
        missing_extensions.join(", ")
    )]
    DroppedTypeExtensions {
        /// The type that is missing extensions.
        typ: String,
        /// The missing extensions.
        missing_extensions: Vec<ExtensionId>,
    },
    /// An extension definition references an extension that is not in the given registry.
    #[display(
        "Extension {extension} depends on dropped extensions {}",
        missing_extensions.join(", ")
    )]
    DroppedTransitiveExtensions {
        /// The extension that is missing dependencies.
        extension: String,
        /// The missing extensions.
        missing_extensions: Vec<ExtensionId>,
    },
}

impl<N: HugrNode> ExtensionCollectionError<N> {
    /// Create a new error when operation extensions have been dropped.
    pub fn dropped_op_extension(
        node: Option<N>,
        op: &OpType,
        missing_extension: impl IntoIterator<Item = ExtensionId>,
    ) -> Self {
        Self::DroppedOpExtensions {
            node,
            op: NamedOp::name(op),
            missing_extensions: missing_extension.into_iter().collect(),
        }
    }

    /// Create a new error when signature extensions have been dropped.
    pub fn dropped_signature(
        signature: &Signature,
        missing_extension: impl IntoIterator<Item = ExtensionId>,
    ) -> Self {
        Self::DroppedSignatureExtensions {
            signature: format!("{signature}"),
            missing_extensions: missing_extension.into_iter().collect(),
        }
    }

    /// Create a new error when signature extensions have been dropped.
    pub fn dropped_type(
        typ: &Type,
        missing_extension: impl IntoIterator<Item = ExtensionId>,
    ) -> Self {
        Self::DroppedTypeExtensions {
            typ: format!("{typ}"),
            missing_extensions: missing_extension.into_iter().collect(),
        }
    }
}

#[cfg(test)]
mod test;
