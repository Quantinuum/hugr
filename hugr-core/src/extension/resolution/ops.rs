//! Resolve `OpaqueOp`s into `ExtensionOp`s and return an operation's required
//! extension.
//!
//! Contains both mutable ([`resolve_op_extensions`]) and immutable
//! ([`collect_operation_extension`]) methods to resolve operations and collect
//! the required extensions respectively.

use std::sync::Arc;

use super::{Extension, ExtensionCollectionError, ExtensionResolutionError};
use crate::Node;
use crate::extension::{ExtensionId, ExtensionRegistry};
use crate::ops::custom::OpaqueOpError;
use crate::ops::{DataflowOpTrait, ExtensionOp, NamedOp, OpType};

/// Returns the extension in the registry required by the operation.
///
/// If the operation does not require an extension, returns `None`.
///
/// [`ExtensionOp`]s store a [`Weak`] reference to their extension, which can be
/// invalidated if the original `Arc<Extension>` is dropped. On such cases, we
/// return an error with the missing extension names.
///
/// # Parameters
///
/// - `node`: The node where the operation is located, if available. This is
///   used to provide context in the error message.
/// - `op`: The operation to collect the extensions from.
pub(crate) fn collect_op_extension(
    node: Option<Node>,
    op: &OpType,
) -> Result<Option<Arc<Extension>>, ExtensionCollectionError> {
    let OpType::ExtensionOp(ext_op) = op else {
        // TODO: Extract the extension when the operation is a `Const`.
        // https://github.com/CQCL/hugr/issues/1742
        return Ok(None);
    };
    let ext = ext_op.def().extension();
    match ext.upgrade() {
        Some(e) => Ok(Some(e)),
        None => Err(ExtensionCollectionError::dropped_op_extension(
            node,
            op,
            [ext_op.def().extension_id().clone()],
        )),
    }
}

/// Compute the required extension for an operation.
///
/// If the op is a [`OpType::OpaqueOp`], replace it with a resolved
/// [`OpType::ExtensionOp`] by searching for the operation in the extension
/// registries.
///
/// If `op` was an opaque or extension operation, the result contains the
/// extension reference that should be added to the hugr's extension registry.
///
/// # Errors
///
/// If the serialized opaque resolves to a definition that conflicts with what
/// was serialized. Or if the operation is not found in the registry.
pub(crate) fn resolve_op_extensions<'e>(
    node: Node,
    op: &mut OpType,
    extensions: &'e ExtensionRegistry,
) -> Result<Option<&'e Arc<Extension>>, ExtensionResolutionError> {
    let ext_not_found_error =
        |ext_id: &ExtensionId, op_id| ExtensionResolutionError::MissingOpExtension {
            node: Some(node),
            op: op_id,
            missing_extension: ext_id.clone(),
            available_extensions: extensions.ids().cloned().collect(),
        };
    let op_not_found_error =
        |extension: &Arc<Extension>, op_id| OpaqueOpError::OpNotFoundInExtension {
            node,
            op: op_id,
            extension: extension.name().clone(),
            available_ops: extension
                .operations()
                .map(|(name, _)| name.clone())
                .collect(),
        };

    match op {
        OpType::ExtensionOp(ext_op) => {
            let ext_id = ext_op.extension_id();
            let ext_version = ext_op.extension_version();

            let extension = extensions
                .get_req(ext_id, Some(&ext_version))
                .ok_or_else(|| ext_not_found_error(ext_id, ext_op.qualified_id()))?;
            let op_def = extension
                .get_op(ext_op.unqualified_id())
                .ok_or_else(|| op_not_found_error(extension, ext_op.qualified_id()))?;

            // Relink the extension operation to an OpDef from the registry.
            //
            // This ensures we don't keep around stale OpDefs that may have
            // their Weak extension reference dropped.
            ext_op
                .relink_def(op_def.clone())
                .map_err(|e| OpaqueOpError::SignatureError {
                    node,
                    name: ext_op.qualified_id(),
                    cause: e,
                })?;

            Ok(Some(extension))
        }
        OpType::OpaqueOp(opaque) => {
            let ext_id = opaque.extension();
            let ext_version = opaque.extension_version();

            let extension = extensions
                .get_req(ext_id, ext_version)
                .ok_or_else(|| ext_not_found_error(ext_id, opaque.qualified_id()))?;
            let op_def = extension
                .get_op(opaque.unqualified_id())
                .ok_or_else(|| op_not_found_error(extension, opaque.qualified_id()))?;

            let ext_op =
                ExtensionOp::new_with_cached(op_def.clone(), opaque.args().to_vec(), opaque)
                    .map_err(|e| OpaqueOpError::SignatureError {
                        node,
                        name: opaque.name().clone(),
                        cause: e,
                    })?;

            if opaque.signature().io() != ext_op.signature().io() {
                return Err(OpaqueOpError::SignatureMismatch {
                    node,
                    extension: opaque.extension().clone(),
                    op: op_def.name().clone(),
                    computed: Box::new(ext_op.signature().into_owned()),
                    stored: Box::new(opaque.signature().into_owned()),
                }
                .into());
            }

            // Replace the opaque operation with the resolved extension operation.
            *op = ext_op.into();

            Ok(Some(extension))
        }
        _ => Ok(None),
    }
}
