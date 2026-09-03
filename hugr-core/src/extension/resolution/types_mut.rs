//! Resolve weak links inside `CustomType`s in an optype's signature, while
//! collecting all used extensions.
//!
//! For a non-mutating option see [`super::collect_op_types_extensions`].

use std::hash::{Hash, Hasher};
use std::sync::Weak;

use rustc_hash::{FxHashMap, FxHashSet};

use super::{ExtensionResolutionError, WeakExtensionRegistry};
use crate::ops::{OpType, Value};
use crate::types::{CustomType, FuncValueType, Signature, SumType, Term, Type, TypeRow, TypeRowRV};
use crate::{Extension, Node};

/// An allocation-identity key that keeps its type storage alive while cached.
///
/// It wraps a [`Type`], but compares and hashes based on the underlying storage
/// pointer rather than the type's structural content.
#[derive(Clone, Eq)]
struct TypeStorageKey(Type);

impl TypeStorageKey {
    /// Creates a key retaining the type's current backing allocation.
    fn new(typ: Type) -> Self {
        Self(typ)
    }
}

impl PartialEq for TypeStorageKey {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0.storage_ptr(), other.0.storage_ptr())
    }
}

impl Hash for TypeStorageKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.storage_ptr().hash(state);
    }
}

/// State shared while resolving type extensions across a HUGR.
///
/// Resolved types are cached by backing-allocation identity. This both avoids
/// retraversing imported types and lets stale siblings reuse the first resolved
/// copy instead of independently cloning their shared term tree.
pub(crate) struct TypeExtensionResolver<'a> {
    extensions: &'a WeakExtensionRegistry,
    used_extensions: WeakExtensionRegistry,
    seen_types: FxHashSet<TypeStorageKey>,
    resolved_types: FxHashMap<TypeStorageKey, Type>,
}

impl<'a> TypeExtensionResolver<'a> {
    /// Creates a resolver for one target extension registry.
    pub(crate) fn new(extensions: &'a WeakExtensionRegistry) -> Self {
        Self {
            extensions,
            used_extensions: WeakExtensionRegistry::default(),
            seen_types: FxHashSet::default(),
            resolved_types: FxHashMap::default(),
        }
    }

    /// Resolves all type references stored in an operation.
    pub(crate) fn resolve_op(
        &mut self,
        node: Option<Node>,
        op: &mut OpType,
    ) -> Result<(), ExtensionResolutionError> {
        match op {
            OpType::ExtensionOp(ext) => {
                for arg in ext.args_mut() {
                    self.resolve_term(node, arg)?;
                }
                self.resolve_signature(node, ext.signature_mut())?;
            }
            OpType::FuncDefn(f) => {
                self.resolve_signature(node, f.signature_mut().body_mut())?;
            }
            OpType::FuncDecl(f) => {
                self.resolve_signature(node, f.signature_mut().body_mut())?;
            }
            OpType::Const(c) => self.resolve_value(node, &mut c.value)?,
            OpType::Input(inp) => self.resolve_type_row(node, &mut inp.types)?,
            OpType::Output(out) => self.resolve_type_row(node, &mut out.types)?,
            OpType::Call(c) => {
                self.resolve_signature(node, c.func_sig.body_mut())?;
                self.resolve_signature(node, &mut c.instantiation)?;
                for arg in &mut c.type_args {
                    self.resolve_term(node, arg)?;
                }
            }
            OpType::CallIndirect(c) => self.resolve_signature(node, &mut c.signature)?,
            OpType::LoadConstant(lc) => self.resolve_type(node, &mut lc.datatype)?,
            OpType::LoadFunction(lf) => {
                self.resolve_signature(node, lf.func_sig.body_mut())?;
                self.resolve_signature(node, &mut lf.instantiation)?;
                for arg in &mut lf.type_args {
                    self.resolve_term(node, arg)?;
                }
            }
            OpType::DFG(dfg) => self.resolve_signature(node, &mut dfg.signature)?,
            OpType::OpaqueOp(op) => {
                for arg in op.args_mut() {
                    self.resolve_term(node, arg)?;
                }
                self.resolve_signature(node, op.signature_mut())?;
            }
            OpType::Tag(t) => {
                for variant in &mut t.variants {
                    self.resolve_type_row(node, variant)?;
                }
            }
            OpType::DataflowBlock(db) => {
                self.resolve_type_row(node, &mut db.inputs)?;
                self.resolve_type_row(node, &mut db.other_outputs)?;
                for row in &mut db.sum_rows {
                    self.resolve_type_row(node, row)?;
                }
            }
            OpType::ExitBlock(e) => self.resolve_type_row(node, &mut e.cfg_outputs)?,
            OpType::TailLoop(tl) => {
                self.resolve_type_row(node, &mut tl.just_inputs)?;
                self.resolve_type_row(node, &mut tl.just_outputs)?;
                self.resolve_type_row(node, &mut tl.rest)?;
            }
            OpType::CFG(cfg) => self.resolve_signature(node, &mut cfg.signature)?,
            OpType::Conditional(cond) => {
                for row in &mut cond.sum_rows {
                    self.resolve_type_row(node, row)?;
                }
                self.resolve_type_row(node, &mut cond.other_inputs)?;
                self.resolve_type_row(node, &mut cond.outputs)?;
            }
            OpType::Case(case) => self.resolve_signature(node, &mut case.signature)?,
            // Ignore optypes that do not store a signature.
            OpType::Module(_) | OpType::AliasDecl(_) | OpType::AliasDefn(_) => {}
        }
        Ok(())
    }

    /// Consumes the resolver and returns all extensions found during resolution.
    pub(crate) fn into_used_extensions(self) -> impl Iterator<Item = Weak<Extension>> + use<> {
        self.used_extensions.into_iter().map(|(_, _, ext)| ext)
    }

    /// Resolves extensions inside a function signature.
    fn resolve_signature(
        &mut self,
        node: Option<Node>,
        signature: &mut Signature,
    ) -> Result<(), ExtensionResolutionError> {
        self.resolve_type_row(node, &mut signature.input)?;
        self.resolve_type_row(node, &mut signature.output)
    }

    /// Resolves extensions inside a runtime function type.
    fn resolve_func_type(
        &mut self,
        node: Option<Node>,
        signature: &mut FuncValueType,
    ) -> Result<(), ExtensionResolutionError> {
        self.resolve_type_row_rv(node, &mut signature.input)?;
        self.resolve_type_row_rv(node, &mut signature.output)
    }

    /// Resolves every type in a closed type row.
    fn resolve_type_row(
        &mut self,
        node: Option<Node>,
        row: &mut TypeRow,
    ) -> Result<(), ExtensionResolutionError> {
        for typ in row.iter_mut() {
            self.resolve_type(node, typ)?;
        }
        Ok(())
    }

    /// Resolves extensions inside a possibly-open runtime type row.
    fn resolve_type_row_rv(
        &mut self,
        node: Option<Node>,
        row: &mut TypeRowRV,
    ) -> Result<(), ExtensionResolutionError> {
        let mut term = Term::from(std::mem::take(row));
        self.resolve_term(node, &mut term)?;
        *row = TypeRowRV::try_from(term)
            .expect("Resolving extensions cannot change kind from ListType(RuntimeType)");
        Ok(())
    }

    /// Resolves one custom type and records its defining extension.
    pub(super) fn resolve_custom_type(
        &mut self,
        node: Option<Node>,
        custom: &mut CustomType,
    ) -> Result<(), ExtensionResolutionError> {
        for arg in custom.args_mut() {
            self.resolve_term(node, arg)?;
        }

        let ext_id = custom.extension();
        let (version, extension) = self
            .extensions
            .get_req(ext_id, custom.extension_version())
            .ok_or_else(|| {
                ExtensionResolutionError::missing_type_extension(
                    node,
                    custom.name(),
                    ext_id,
                    self.extensions,
                )
            })?;

        self.used_extensions
            .register(ext_id.clone(), version.clone(), extension.clone());
        custom.update_extension(extension.clone());
        Ok(())
    }

    /// Resolves one runtime type, reusing work for shared backing allocations.
    pub(super) fn resolve_type(
        &mut self,
        node: Option<Node>,
        typ: &mut Type,
    ) -> Result<(), ExtensionResolutionError> {
        let original_key = TypeStorageKey::new(typ.clone());
        if self.seen_types.contains(&original_key) {
            return Ok(());
        }
        if let Some(resolved) = self.resolved_types.get(&original_key) {
            typ.clone_from(resolved);
            return Ok(());
        }

        if self.collect_current_type_extensions(typ) {
            self.seen_types.insert(original_key);
            return Ok(());
        }

        self.resolve_term(node, typ.term_mut())?;

        // Map stale siblings to the resolved value and record its new backing
        // allocation as already traversed.
        let resolved_key = TypeStorageKey::new(typ.clone());
        self.resolved_types.insert(original_key, typ.clone());
        self.seen_types.insert(resolved_key);
        Ok(())
    }

    /// Collects references from a type only if they match the target registry.
    fn collect_current_type_extensions(&mut self, typ: &Type) -> bool {
        let mut current_extensions = WeakExtensionRegistry::default();
        if !collect_current_term_extensions(typ, self.extensions, &mut current_extensions) {
            return false;
        }

        for (id, version, extension) in current_extensions {
            self.used_extensions.register(id, version, extension);
        }
        true
    }

    /// Resolves extensions recursively inside an arbitrary term.
    pub(super) fn resolve_term(
        &mut self,
        node: Option<Node>,
        term: &mut Term,
    ) -> Result<(), ExtensionResolutionError> {
        match term {
            Term::ExtensionType(custom) => self.resolve_custom_type(node, custom)?,
            Term::FunctionType(function) => self.resolve_func_type(node, function)?,
            Term::SumType(SumType::General(general)) => {
                for row in general.rows_mut() {
                    self.resolve_type_row_rv(node, row)?;
                }
            }
            Term::ConstKind(typ) => self.resolve_type(node, typ)?,
            Term::List(children)
            | Term::ListConcat(children)
            | Term::Tuple(children)
            | Term::TupleConcat(children) => {
                for child in children.iter_mut() {
                    self.resolve_term(node, child)?;
                }
            }
            Term::ListKind(item_type) => self.resolve_term(node, item_type.as_mut())?,
            Term::TupleKind(item_types) => self.resolve_term(node, item_types.as_mut())?,
            Term::Variable(_)
            | Term::TypeKind(_)
            | Term::StaticKind
            | Term::BoundedNatKind(_)
            | Term::StringKind
            | Term::BytesKind
            | Term::FloatKind
            | Term::BoundedNat(_)
            | Term::String(_)
            | Term::Bytes(_)
            | Term::Float(_)
            | Term::SumType(SumType::Unit { .. }) => {}
        }
        Ok(())
    }

    /// Resolves extensions recursively inside a constant value.
    pub(super) fn resolve_value(
        &mut self,
        node: Option<Node>,
        value: &mut Value,
    ) -> Result<(), ExtensionResolutionError> {
        match value {
            Value::Extension { e } => {
                e.value_mut().update_extensions(self.extensions)?;

                // Custom constants may contain types resolved from local extensions rather than the
                // extension registry being collected.
                // We force a resolution against the target registry here.
                let mut typ = e.get_type();
                self.resolve_type(node, &mut typ)?;
            }
            Value::Sum(sum) => {
                if let SumType::General(general) = &mut sum.sum_type {
                    for row in general.rows_mut() {
                        self.resolve_type_row_rv(node, row)?;
                    }
                }
                for value in &mut sum.values {
                    self.resolve_value(node, value)?;
                }
            }
        }
        Ok(())
    }
}

/// Resolves a function type while merging its extensions into an existing
/// accumulator used by extension-definition loading.
pub(super) fn resolve_func_type_exts(
    node: Option<Node>,
    signature: &mut FuncValueType,
    extensions: &WeakExtensionRegistry,
    used_extensions: &mut WeakExtensionRegistry,
) -> Result<(), ExtensionResolutionError> {
    let mut resolver = TypeExtensionResolver::new(extensions);
    resolver.resolve_func_type(node, signature)?;
    for (id, version, extension) in resolver.used_extensions {
        used_extensions.register(id, version, extension);
    }
    Ok(())
}

/// Replace extension pointers in an optype using a standalone resolver.
///
/// Returns an iterator over the used extensions. HUGR-wide resolution uses a
/// shared [`TypeExtensionResolver`] directly so its type cache spans all ops.
#[cfg(test)]
pub(super) fn resolve_op_types_extensions(
    node: Option<Node>,
    op: &mut OpType,
    extensions: &WeakExtensionRegistry,
) -> Result<impl Iterator<Item = Weak<Extension>> + use<>, ExtensionResolutionError> {
    let mut resolver = TypeExtensionResolver::new(extensions);
    resolver.resolve_op(node, op)?;
    Ok(resolver.into_used_extensions())
}

/// Collects extension references while verifying that they match a registry.
///
/// Results are accumulated separately and committed only when the complete
/// term matches, keeping the already-resolved fast path to one traversal.
fn collect_current_term_extensions(
    term: &Term,
    extensions: &WeakExtensionRegistry,
    used_extensions: &mut WeakExtensionRegistry,
) -> bool {
    match term {
        Term::ExtensionType(custom) => {
            if !custom
                .args()
                .iter()
                .all(|arg| collect_current_term_extensions(arg, extensions, used_extensions))
            {
                return false;
            }

            let current = custom.extension_ref();
            let Some(extension) = current.upgrade() else {
                return false;
            };
            let Some((_, expected)) =
                extensions.get_req(custom.extension(), custom.extension_version())
            else {
                return false;
            };
            if !current.ptr_eq(expected) {
                return false;
            }

            used_extensions.register(
                extension.name().clone(),
                extension.version().clone(),
                current,
            );
            true
        }
        Term::FunctionType(function) => {
            collect_current_term_extensions(&function.input, extensions, used_extensions)
                && collect_current_term_extensions(&function.output, extensions, used_extensions)
        }
        Term::SumType(SumType::General(general)) => general
            .rows()
            .iter()
            .all(|row| collect_current_term_extensions(row, extensions, used_extensions)),
        Term::ConstKind(typ) => collect_current_term_extensions(typ, extensions, used_extensions),
        Term::List(children)
        | Term::ListConcat(children)
        | Term::Tuple(children)
        | Term::TupleConcat(children) => children
            .iter()
            .all(|child| collect_current_term_extensions(child, extensions, used_extensions)),
        Term::ListKind(item_type) => {
            collect_current_term_extensions(item_type, extensions, used_extensions)
        }
        Term::TupleKind(item_types) => {
            collect_current_term_extensions(item_types, extensions, used_extensions)
        }
        Term::Variable(_)
        | Term::TypeKind(_)
        | Term::StaticKind
        | Term::BoundedNatKind(_)
        | Term::StringKind
        | Term::BytesKind
        | Term::FloatKind
        | Term::BoundedNat(_)
        | Term::String(_)
        | Term::Bytes(_)
        | Term::Float(_)
        | Term::SumType(SumType::Unit { .. }) => true,
    }
}
