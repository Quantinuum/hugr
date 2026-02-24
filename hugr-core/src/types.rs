//! General wire types used in the compiler

mod check;
pub mod custom;
mod poly_func;
pub(crate) mod serialize;
mod signature;
pub mod type_param;
pub mod type_row;

use crate::extension::resolution::{
    ExtensionCollectionError, WeakExtensionRegistry, collect_term_exts,
};
pub use crate::ops::constant::{ConstTypeError, CustomCheckFailure};
use crate::types::type_param::{TermTypeError, check_term_type};
use crate::utils::display_list_with_separator;
pub use check::SumTypeError;
pub use custom::CustomType;
pub use poly_func::{PolyFuncType, PolyFuncTypeRV};
pub use signature::{FuncValueType, Signature};
use smol_str::SmolStr;
pub use type_param::{Term, TypeArg};
pub use type_row::{TypeRow, TypeRowRV};

use itertools::FoldWhile::{Continue, Done};
use itertools::{Either, Itertools as _};
#[cfg(test)]
use proptest_derive::Arbitrary;
use serde::{Deserialize, Serialize};
use std::ops::Deref;

use crate::extension::{ExtensionRegistry, ExtensionSet, SignatureError};

use self::type_param::TypeParam;

/// A unique identifier for a type.
pub type TypeName = SmolStr;

/// Slice of a [`TypeName`] type identifier.
pub type TypeNameRef = str;

/// The kinds of edges in a HUGR, excluding Hierarchy.
#[derive(
    Clone, PartialEq, Eq, Debug, serde::Serialize, serde::Deserialize, derive_more::Display,
)]
#[non_exhaustive]
pub enum EdgeKind {
    /// Control edges of a CFG region.
    ControlFlow,
    /// Data edges of a DDG region, also known as "wires".
    Value(Type),
    /// A reference to a static constant value - must be a Copyable type
    Const(Type),
    /// A reference to a function i.e. [`FuncDecl`] or [`FuncDefn`].
    ///
    /// [`FuncDecl`]: crate::ops::FuncDecl
    /// [`FuncDefn`]: crate::ops::FuncDefn
    Function(PolyFuncType),
    /// Explicitly enforce an ordering between nodes in a DDG.
    StateOrder,
}

impl EdgeKind {
    /// Returns whether the type might contain linear data.
    #[must_use]
    pub fn is_linear(&self) -> bool {
        matches!(self, EdgeKind::Value(t) if !t.copyable())
    }

    /// Whether this `EdgeKind` represents a Static edge (in the spec)
    /// - i.e. the value is statically known
    #[must_use]
    pub fn is_static(&self) -> bool {
        matches!(self, EdgeKind::Const(_) | EdgeKind::Function(_))
    }

    /// Returns `true` if the edge kind is [`ControlFlow`].
    ///
    /// [`ControlFlow`]: EdgeKind::ControlFlow
    #[must_use]
    pub fn is_control_flow(&self) -> bool {
        matches!(self, Self::ControlFlow)
    }

    /// Returns `true` if the edge kind is [`Value`].
    ///
    /// [`Value`]: EdgeKind::Value
    #[must_use]
    pub fn is_value(&self) -> bool {
        matches!(self, Self::Value(..))
    }

    /// Returns `true` if the edge kind is [`Const`].
    ///
    /// [`Const`]: EdgeKind::Const
    #[must_use]
    pub fn is_const(&self) -> bool {
        matches!(self, Self::Const(..))
    }

    /// Returns `true` if the edge kind is [`Function`].
    ///
    /// [`Function`]: EdgeKind::Function
    #[must_use]
    pub fn is_function(&self) -> bool {
        matches!(self, Self::Function(..))
    }

    /// Returns `true` if the edge kind is [`StateOrder`].
    ///
    /// [`StateOrder`]: EdgeKind::StateOrder
    #[must_use]
    pub fn is_state_order(&self) -> bool {
        matches!(self, Self::StateOrder)
    }
}

#[derive(
    Copy, Default, Clone, PartialEq, Eq, Hash, Debug, derive_more::Display, Serialize, Deserialize,
)]
#[cfg_attr(test, derive(Arbitrary))]
/// Bounds on the valid operations on a type in a HUGR program.
pub enum TypeBound {
    /// The type can be copied in the program.
    #[serde(rename = "C", alias = "E")] // alias to read in legacy Eq variants
    Copyable,
    /// No bound on the type.
    ///
    /// It cannot be copied nor discarded.
    #[serde(rename = "A")]
    #[default]
    Linear,
}

impl TypeBound {
    /// Returns the smallest `TypeTag` containing both the receiver and argument.
    /// (This will be one of the receiver or the argument.)
    #[must_use]
    pub fn union(self, other: Self) -> Self {
        if self.contains(other) {
            self
        } else {
            debug_assert!(other.contains(self));
            other
        }
    }

    /// Report if this bound contains another.
    #[must_use]
    pub const fn contains(&self, other: TypeBound) -> bool {
        use TypeBound::{Copyable, Linear};
        matches!((self, other), (Linear, _) | (_, Copyable))
    }
}

/// Calculate the least upper bound for an iterator of bounds
pub(crate) fn least_upper_bound(mut tags: impl Iterator<Item = TypeBound>) -> TypeBound {
    tags.fold_while(TypeBound::Copyable, |acc, new| {
        if acc == TypeBound::Linear || new == TypeBound::Linear {
            Done(TypeBound::Linear)
        } else {
            Continue(acc.union(new))
        }
    })
    .into_inner()
}

#[derive(Clone, Debug, Eq, Serialize, Deserialize)]
#[serde(tag = "s")]
#[non_exhaustive]
/// Representation of a Sum type.
/// Either store the types of the variants, or in the special (but common) case
/// of a `UnitSum` (sum over empty tuples), store only the size of the Sum.
pub enum SumType {
    /// Special case of a Sum over unit types.
    #[allow(missing_docs)]
    Unit { size: u8 },
    /// General case of a Sum type.
    #[allow(missing_docs)]
    General(GeneralSum),
}

/// General case of a [SumType]. Prefer using [SumType::new] and friends.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneralSum {
    /// Each term here must be an instance of [Term::ListType]([Term::RuntimeType]), being
    /// the elements of exactly one variant. (Thus, this explicitly forbids sums with an
    /// unknown number of variants.)
    // We could just have a single `rows: Term` here, an instance of
    //`Term::ListType(Term::ListType(Term::RuntimeType))`, but then many functions like
    // `len` and `variants` would be impossible. (We might want a separate "FixedAritySum"
    // rust type supporting those, with try_from(SumType).)
    rows: Vec<Term>,
}

impl GeneralSum {
    /// Initialize a new general sum type. (Note the number of variants is fixed.)
    ///
    /// # Panics
    ///
    /// If any element of `rows` is not a list (perhaps of variable length) of runtime types.
    /// See [Self::try_new] or [Self::new_unchecked] for alternatives.
    pub fn new(rows: impl Into<Vec<Term>>) -> Self {
        Self::try_new(rows).unwrap()
    }

    /// Initialize a new general sum type, checking that each variant is a list of runtime types.
    ///
    /// # Errors
    ///
    /// If any element of `rows` is not a list (perhaps of variable length) of runtime types.
    pub fn try_new(rows: impl Into<Vec<Term>>) -> Result<Self, TermTypeError> {
        let rows = rows.into();
        for row in rows.iter() {
            check_term_type(row, &Term::new_list_type(TypeBound::Linear))?;
        }
        Ok(Self::new_unchecked(rows))
    }

    /// Initialize a new general sum type without checking the variants.
    pub fn new_unchecked(rows: impl Into<Vec<Term>>) -> Self {
        let rows: Vec<Term> = rows.into();
        Self { rows }
    }

    /// Returns an iterator over the variants, each an instance of [Term::ListType]`(`[Term::RuntimeType]`)`
    pub fn iter(&self) -> impl Iterator<Item = &Term> {
        self.rows.iter()
    }

    /// Returns a mutable iterator over the variants, each should be an instance
    /// of [Term::ListType]`(`[Term::RuntimeType]`)` but of course `iter_mut` allows
    /// bypassing such checks.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Term> {
        self.rows.iter_mut()
    }
}

impl std::hash::Hash for SumType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.variants().for_each(|v| v.hash(state));
    }
}

impl PartialEq for SumType {
    fn eq(&self, other: &Self) -> bool {
        self.num_variants() == other.num_variants() && self.variants().eq(other.variants())
    }
}

impl std::fmt::Display for SumType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.num_variants() == 0 {
            return write!(f, "⊥");
        }

        match self {
            SumType::Unit { size: 1 } => write!(f, "Unit"),
            SumType::Unit { size: 2 } => write!(f, "Bool"),
            SumType::Unit { size } => {
                display_list_with_separator(itertools::repeat_n("[]", *size as usize), f, "+")
            }
            SumType::General(GeneralSum { rows, .. }) => match rows.len() {
                1 if rows[0].is_empty_list() => write!(f, "Unit"),
                2 if rows[0].is_empty_list() && rows[1].is_empty_list() => write!(f, "Bool"),
                _ => display_list_with_separator(rows.iter(), f, "+"),
            },
        }
    }
}

impl SumType {
    /// Initialize a new sum type.
    ///
    /// # Panics
    ///
    /// If any element of `variants` is not a list (perhaps of variable length) of runtime types.
    /// See [Self::try_new] or [Self::new_unchecked] for alternatives.
    pub fn new<V>(variants: impl IntoIterator<Item = V>) -> Self
    where
        V: Into<Term>,
    {
        Self::try_new(variants).unwrap()
    }

    /// Initialize a new sum type, checking that each variant is a list of runtime types.
    ///
    /// # Errors
    ///
    /// If any element of `variants` is not a list (perhaps of variable length) of runtime types.
    /// See [Self::new_unchecked] for an alternative.
    pub fn try_new<V: Into<Term>>(
        variants: impl IntoIterator<Item = V>,
    ) -> Result<Self, TermTypeError> {
        let variants = variants.into_iter().map(V::into).collect_vec();
        let len = variants.len();
        if u8::try_from(len).is_ok() && variants.iter().all(Term::is_empty_list) {
            Ok(Self::new_unary(len as u8))
        } else {
            GeneralSum::try_new(variants).map(Self::General)
        }
    }

    /// Initialize a new sum type without checking the variants.
    pub fn new_unchecked<V: Into<Term>>(variants: impl IntoIterator<Item = V>) -> Self {
        let variants = variants.into_iter().map_into().collect::<Vec<_>>();
        let len: usize = variants.len();
        if u8::try_from(len).is_ok() && variants.iter().all(Term::is_empty_list) {
            Self::new_unary(len as u8)
        } else {
            Self::General(GeneralSum::new_unchecked(variants))
        }
    }

    /// New `UnitSum` with empty Tuple variants.
    #[must_use]
    pub const fn new_unary(size: u8) -> Self {
        Self::Unit { size }
    }

    /// New tuple (single row of variants).
    ///
    /// # Panics
    ///
    /// If the argument is not of type [Term::ListType]`(`[Term::RuntimeType]`)`
    pub fn new_tuple(types: impl Into<Term>) -> Self {
        Self::new([types.into()])
    }

    /// New option type (either an empty option, or a row of types).
    pub fn new_option(types: impl Into<TypeRow>) -> Self {
        Self::new([vec![].into(), types.into()])
    }

    /// Report the tag'th variant, if it exists.
    #[must_use]
    pub fn get_variant(&self, tag: usize) -> Option<&Term> {
        match self {
            SumType::Unit { size } if tag < (*size as usize) => Some(Term::EMPTY_LIST_REF),
            SumType::General(GeneralSum { rows, .. }) => rows.get(tag),
            _ => None,
        }
    }

    /// Returns the number of variants in the sum type.
    #[must_use]
    pub fn num_variants(&self) -> usize {
        match self {
            SumType::Unit { size } => *size as usize,
            SumType::General(GeneralSum { rows, .. }) => rows.len(),
        }
    }

    /// Returns variant row if there is only one variant
    /// (will be an instance of [Term::ListType]([Term::RuntimeType]).
    #[must_use]
    pub fn as_tuple(&self) -> Option<&Term> {
        match self {
            SumType::Unit { size } if *size == 1 => Some(Term::EMPTY_LIST_REF),
            SumType::General(GeneralSum { rows, .. }) if rows.len() == 1 => Some(&rows[0]),
            _ => None,
        }
    }

    /// If the sum matches the convention of `Option[row]`, return the row
    /// (an instance of [Term::ListType]([Term::RuntimeType]).
    #[must_use]
    pub fn as_option(&self) -> Option<&Term> {
        match self {
            SumType::Unit { size } if *size == 2 => Some(Term::EMPTY_LIST_REF),
            SumType::General(GeneralSum { rows, .. })
                if rows.len() == 2 && rows[0].is_empty_list() =>
            {
                Some(&rows[1])
            }
            _ => None,
        }
    }

    // ALAN removing as_unary_option.
    // "If a sum is an option of a single type, return the type. pub fn as_unary_option(&self) -> Option<&TypeRV>"
    // But of course a TypeRV was not necessarily a single type...

    /// Returns an iterator over the variants, each an instance of [Term::ListType]`(`[Term::RuntimeType]`)`
    pub fn variants(&self) -> impl Iterator<Item = &Term> {
        match self {
            SumType::Unit { size } => {
                Either::Left(itertools::repeat_n(Term::EMPTY_LIST_REF, *size as usize))
            }
            SumType::General(gs) => Either::Right(gs.iter()),
        }
    }

    fn bound(&self) -> TypeBound {
        match self {
            SumType::Unit { .. } => TypeBound::Copyable,
            SumType::General(GeneralSum { rows }) => {
                if rows
                    .iter()
                    .all(|t| check_term_type(t, &Term::new_list_type(TypeBound::Copyable)).is_ok())
                {
                    TypeBound::Copyable
                } else {
                    // That all elements were types was checked in the GeneralSum constructor.
                    // That may have been bypassed via GeneralSum::new_unchecked, but do no
                    // check here (we will do so in validate()).
                    TypeBound::Linear
                }
            }
        }
    }
}

impl Transformable for SumType {
    fn transform<T: TypeTransformer>(&mut self, tr: &T) -> Result<bool, T::Err> {
        match self {
            SumType::Unit { .. } => Ok(false),
            SumType::General(GeneralSum { rows }) => rows.transform(tr),
        }
    }
}

impl From<SumType> for Type {
    fn from(sum: SumType) -> Self {
        match sum {
            SumType::Unit { size } => Type::new_unit_sum(size),
            SumType::General(GeneralSum { rows }) => Type::new_sum(rows),
        }
    }
}

#[derive(
    Clone, Debug, Eq, Hash, PartialEq, derive_more::Display, serde::Serialize, serde::Deserialize,
)]
#[display("{_0}")]
#[serde(
    into = "serialize::SerSimpleType",
    try_from = "serialize::SerSimpleType"
)]
/// A HUGR type - a single value, that can be sent down a wire.
///
/// The valid types of [`EdgeKind::Value`] and [`EdgeKind::Const`] edges.
/// Such an edge is valid if the ports on either end agree on the [Type].
/// Types have a [`TypeBound`] which specifies the number of inports
/// to which a particular outport (of that type) may be connected.
///
/// Examples:
/// ```
/// # use hugr::types::{Type, TypeBound};
/// # use hugr::type_row;
///
/// let sum = Type::new_sum([type_row![], type_row![]]);
/// assert_eq!(sum.least_upper_bound(), TypeBound::Copyable);
/// ```
///
/// ```
/// # use hugr::types::{Type, TypeBound, Signature};
///
/// let func_type: Type = Type::new_function(Signature::new_endo([]));
/// assert_eq!(func_type.least_upper_bound(), TypeBound::Copyable);
/// ```
pub struct Type(Term, TypeBound);

/// Legacy alias (for a list of types) - not statically checked.
pub type TypeRV = Term;

impl Type {
    /// An empty `TypeRow` or `TypeRowRV`. Provided here for convenience
    pub const EMPTY_TYPEROW: TypeRow = TypeRow::new();
    /// Unit type (empty tuple).
    pub const UNIT: Self = Self(
        Term::RuntimeSum(SumType::Unit { size: 1 }),
        TypeBound::Copyable,
    );

    /// Initialize a new function type.
    pub fn new_function(fun_ty: impl Into<FuncValueType>) -> Self {
        Self(
            Term::RuntimeFunction(Box::new(fun_ty.into())),
            TypeBound::Copyable,
        )
    }

    /// Initialize a new tuple type by providing the elements.
    #[inline(always)]
    pub fn new_tuple(types: impl Into<Term>) -> Self {
        let row = types.into();
        match row.is_empty_list() {
            true => Self::UNIT,
            false => Self::new_sum([row]),
        }
    }

    /// Initialize a new sum type by providing the possible variant types.
    ///
    /// # Panics
    ///
    /// If any element is not a type or row variable
    #[inline(always)]
    pub fn new_sum<R>(variants: impl IntoIterator<Item = R>) -> Self
    where
        R: Into<TypeRowRV>,
    {
        let st = SumType::new(variants);
        let b = st.bound();
        Self(Term::RuntimeSum(st), b)
    }

    /// Initialize a new custom type.
    // TODO remove? Extensions/TypeDefs should just provide `Type` directly
    #[must_use]
    pub const fn new_extension(opaque: CustomType) -> Self {
        let bound = opaque.bound();
        Self(Term::RuntimeExtension(opaque), bound)
    }

    /// New `UnitSum` with empty Tuple variants
    #[must_use]
    pub const fn new_unit_sum(size: u8) -> Self {
        // should be the only way to avoid going through SumType::new
        Self(
            Term::RuntimeSum(SumType::new_unary(size)),
            TypeBound::Copyable,
        )
    }

    /// New use (occurrence) of the type variable with specified index.
    /// `bound` must be exactly that with which the variable was declared
    /// (i.e. as a [`Term::RuntimeType`]`(bound)`), which may be narrower
    /// than required for the use.
    #[must_use]
    pub fn new_var_use(idx: usize, bound: TypeBound) -> Self {
        Self(Term::new_var_use(idx, bound), bound)
    }

    /// Report the least upper [`TypeBound`]
    #[inline(always)]
    pub const fn least_upper_bound(&self) -> TypeBound {
        self.1
    }

    /// Returns the inner [`SumType`] if the type is a sum.
    pub fn as_sum(&self) -> Option<&SumType> {
        match &self.0 {
            Term::RuntimeSum(s) => Some(s),
            _ => None,
        }
    }

    /// Returns the inner [`CustomType`] if the type is from an extension.
    // ALAN if we put this on Term, does Deref allow calling it on Type?
    pub fn as_extension(&self) -> Option<&CustomType> {
        match &self.0 {
            Term::RuntimeExtension(ct) => Some(ct),
            _ => None,
        }
    }

    /// Report if the type is copyable - i.e.the least upper bound of the type
    /// is contained by the copyable bound.
    pub const fn copyable(&self) -> bool {
        TypeBound::Copyable.contains(self.least_upper_bound())
    }

    /// Checks all variables used in the type are in the provided list
    /// of bound variables, and that for each [`CustomType`] the type arguments
    /// [validate] and fit into the declared parameters of the [`TypeDef`]
    ///
    /// [validate]: crate::types::type_param::TypeArg::validate
    /// [TypeDef]: crate::extension::TypeDef
    pub(crate) fn validate(&self, var_decls: &[TypeParam]) -> Result<(), SignatureError> {
        self.0.validate(var_decls)?;
        check_term_type(&self.0, &self.1.into())?;
        debug_assert!(
            self.1 == TypeBound::Copyable
                || check_term_type(&self.0, &TypeBound::Copyable.into()).is_err()
        );
        Ok(())
    }

    /// Applies a substitution to a type.
    /// This may result in a row of types, if this [Type] is not really a single type but actually a row variable
    /// Invariants may be confirmed by validation:
    /// * If [`Type::validate`]`(false)` returns successfully, this method will return a Vec containing exactly one type
    /// * If [`Type::validate`]`(false)` fails, but `(true)` succeeds, this method may (depending on structure of self)
    ///   return a Vec containing any number of [Type]s. These may (or not) pass [`Type::validate`]
    fn substitute(&self, s: &Substitution) -> Self {
        let t = self.0.substitute(s);
        // Must succeed and produce a type assuming substitution valid (RHSes
        // fit within LHS). However, may *narrow* the bound, so recompute.
        let b = t.least_upper_bound().unwrap();
        Self(t, b)
    }

    /// Returns a registry with the concrete extensions used by this type.
    ///
    /// This includes the extensions of custom types that may be nested
    /// inside other types.
    pub fn used_extensions(&self) -> Result<ExtensionRegistry, ExtensionCollectionError> {
        let mut used = WeakExtensionRegistry::default();
        let mut missing = ExtensionSet::new();

        collect_term_exts(self, &mut used, &mut missing);

        if missing.is_empty() {
            Ok(used.try_into().expect("all extensions are present"))
        } else {
            Err(ExtensionCollectionError::dropped_type(self, missing))
        }
    }
}

impl Deref for Type {
    type Target = Term;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl TryFrom<Term> for Type {
    type Error = TermTypeError;

    fn try_from(t: Term) -> Result<Self, TermTypeError> {
        match t.least_upper_bound() {
            Some(b) => Ok(Self(t, b)),
            None => Err(TermTypeError::TypeMismatch {
                term: Box::new(t),
                type_: Box::new(TypeBound::Linear.into()),
            }),
        }
    }
}

impl From<Type> for Term {
    fn from(t: Type) -> Self {
        t.0
    }
}

impl Transformable for Type {
    fn transform<T: TypeTransformer>(&mut self, tr: &T) -> Result<bool, T::Err> {
        let res = self.0.transform(tr)?;
        if res {
            self.1 = self.0.least_upper_bound().unwrap()
        }
        Ok(res)
    }
}

/// Details a replacement of type variables with a finite list of known values.
/// (Variables out of the range of the list will result in a panic)
#[derive(Clone, Debug, derive_more::Display)]
#[display("[{}]", _0.iter().map(std::string::ToString::to_string).join(", "))]
pub struct Substitution<'a>(&'a [TypeArg]);

impl<'a> Substitution<'a> {
    /// Create a new Substitution given the replacement values (indexed
    /// as the variables they replace). `exts` must contain the [`TypeDef`]
    /// for every custom [Type] (to which the Substitution is applied)
    /// containing a type-variable.
    ///
    /// [`TypeDef`]: crate::extension::TypeDef
    #[must_use]
    pub fn new(items: &'a [TypeArg]) -> Self {
        Self(items)
    }

    pub(crate) fn apply_var(&self, idx: usize, decl: &TypeParam) -> TypeArg {
        let arg = self
            .0
            .get(idx)
            .expect("Undeclared type variable - call validate() ?");
        debug_assert_eq!(check_term_type(arg, decl), Ok(()));
        arg.clone()
    }
}

/// A transformation that can be applied to a [Type] or [`TypeArg`].
///
/// More general in some ways than a Substitution: can fail with a
/// [`Self::Err`],  may change [`TypeBound::Copyable`] to [`TypeBound::Linear`],
/// and applies to arbitrary extension types rather than type variables.
pub trait TypeTransformer {
    /// Error returned when a [`CustomType`] cannot be transformed, or a type
    /// containing it (e.g. if changing a runtime type from copyable to
    /// linear invalidates a parameterized type).
    type Err: std::error::Error + From<SignatureError>;

    /// Applies the transformation to an extension type.
    ///
    /// Note that if the [`CustomType`] has type arguments, these will *not*
    /// have been transformed first (this might not produce a valid type
    /// due to changes in [`TypeBound`]).
    ///
    /// Returns a type to use instead, or None to indicate no change
    ///   (in which case, the `TypeArgs` will be transformed instead.
    ///    To prevent transforming the arguments, return `t.clone().into()`.)
    fn apply_custom(&self, t: &CustomType) -> Result<Option<Type>, Self::Err>;

    // Note: in future releases more methods may be added here to transform other types.
    // By defaulting such trait methods to Ok(None), backwards compatibility will be preserved.
}

/// Trait for things that can be transformed by applying a [`TypeTransformer`].
/// (A destructive / in-place mutation.)
pub trait Transformable {
    /// Applies a [`TypeTransformer`] to this instance.
    ///
    /// Returns true if any part may have changed, or false for definitely no change.
    ///
    /// If an Err occurs, `self` may be left in an inconsistent state (e.g. partially
    /// transformed).
    fn transform<T: TypeTransformer>(&mut self, t: &T) -> Result<bool, T::Err>;
}

impl<E: Transformable> Transformable for [E] {
    fn transform<T: TypeTransformer>(&mut self, tr: &T) -> Result<bool, T::Err> {
        let mut any_change = false;
        for item in self {
            any_change |= item.transform(tr)?;
        }
        Ok(any_change)
    }
}

#[cfg(test)]
pub(crate) mod test {
    use std::hash::{Hash, Hasher};
    use std::sync::Weak;

    use super::*;
    use crate::extension::TypeDefBound;
    use crate::extension::prelude::{option_type, qb_t, usize_t};
    use crate::std_extensions::collections::array::{array_type, array_type_parametric};
    use crate::std_extensions::collections::list::list_type;
    use crate::types::type_param::TermTypeError;
    use crate::{Extension, hugr::IdentList, type_row};

    #[test]
    fn construct() {
        let t: Type = Type::new_tuple(vec![
            usize_t(),
            Type::new_function(Signature::new_endo([])),
            Type::new_extension(CustomType::new(
                "my_custom",
                [],
                "my_extension".try_into().unwrap(),
                TypeBound::Copyable,
                // Dummy extension reference.
                &Weak::default(),
            )),
            //Type::new_alias(AliasDecl::new("my_alias", TypeBound::Copyable)),
        ]);
        assert_eq!(&t.to_string(), "[usize, [] -> [], my_custom]");
    }

    #[rstest::rstest]
    fn sum_construct() {
        let pred1 = Type::new_sum([type_row![], type_row![]]);
        let pred2 = Type::new_unit_sum(2);

        assert_eq!(pred1, pred2);

        let pred_direct = SumType::Unit { size: 2 };
        assert_eq!(pred1, Type::from(pred_direct));
    }

    #[test]
    fn as_sum() {
        let t = Type::new_unit_sum(0);
        assert!(t.as_sum().is_some());
    }

    #[test]
    fn as_option() {
        let opt = option_type([usize_t()]);

        assert_eq!(
            opt.as_option().unwrap().clone(),
            Term::new_list([usize_t().into()])
        );
        assert_eq!(Type::new_unit_sum(2).as_sum().unwrap().as_option(), None);

        assert_eq!(
            Type::new_tuple(vec![usize_t()])
                .as_sum()
                .unwrap()
                .as_option(),
            None
        );
    }

    #[test]
    fn as_extension() {
        assert_eq!(
            Type::new_extension(usize_t().as_extension().unwrap().clone()),
            usize_t()
        );
        assert_eq!(Type::new_unit_sum(0).as_extension(), None);
    }

    #[test]
    fn sum_variants() {
        let variants: Vec<TypeRowRV> = vec![
            [Type::UNIT].into(),
            vec![TypeRV::new_row_var_use(0, TypeBound::Linear)].into(),
        ];
        let t = SumType::new(variants.clone());
        assert_eq!(variants, t.variants().cloned().collect_vec());

        let empty_rows = vec![Term::EMPTY_LIST; 3];
        let sum_unary = SumType::new_unary(3);
        assert_eq!(empty_rows, sum_unary.variants().cloned().collect_vec());
        let sum_general = SumType::General(GeneralSum::new(empty_rows));
        assert_eq!(sum_general, sum_unary);

        let mut hasher_general = std::hash::DefaultHasher::new();
        sum_general.hash(&mut hasher_general);
        let mut hasher_unary = std::hash::DefaultHasher::new();
        sum_unary.hash(&mut hasher_unary);
        assert_eq!(hasher_general.finish(), hasher_unary.finish());
    }

    pub(super) struct FnTransformer<T>(pub(super) T);
    impl<T: Fn(&CustomType) -> Option<Type>> TypeTransformer for FnTransformer<T> {
        type Err = SignatureError;

        fn apply_custom(&self, t: &CustomType) -> Result<Option<Type>, Self::Err> {
            Ok((self.0)(t))
        }
    }
    #[test]
    fn transform() {
        const LIN: SmolStr = SmolStr::new_inline("MyLinear");
        let e = Extension::new_test_arc(IdentList::new("TestExt").unwrap(), |e, w| {
            e.add_type(LIN, vec![], String::new(), TypeDefBound::any(), w)
                .unwrap();
        });
        let lin = e.get_type(&LIN).unwrap().instantiate([]).unwrap();

        let lin_to_usize = FnTransformer(|ct: &CustomType| (*ct == lin).then_some(usize_t()));
        let mut t = Type::new_extension(lin.clone());
        assert_eq!(t.transform(&lin_to_usize), Ok(true));
        assert_eq!(t, usize_t());

        for coln in [
            list_type,
            |t| array_type(10, t),
            |t| {
                array_type_parametric(
                    TypeArg::new_var_use(0, TypeParam::bounded_nat_type(3.try_into().unwrap())),
                    t,
                )
                .unwrap()
            },
        ] {
            let mut t = coln(lin.clone().into());
            assert_eq!(t.transform(&lin_to_usize), Ok(true));
            let expected = coln(usize_t());
            assert_eq!(t, expected);
            assert_eq!(t.transform(&lin_to_usize), Ok(false));
            assert_eq!(t, expected);
        }
    }

    #[test]
    fn transform_copyable_to_linear() {
        const CPY: SmolStr = SmolStr::new_inline("MyCopyable");
        const COLN: SmolStr = SmolStr::new_inline("ColnOfCopyableElems");
        let e = Extension::new_test_arc(IdentList::new("TestExt").unwrap(), |e, w| {
            e.add_type(CPY, vec![], String::new(), TypeDefBound::copyable(), w)
                .unwrap();
            e.add_type(
                COLN,
                vec![TypeParam::new_list_type(TypeBound::Copyable)],
                String::new(),
                TypeDefBound::copyable(),
                w,
            )
            .unwrap();
        });

        let cpy = e.get_type(&CPY).unwrap().instantiate([]).unwrap();
        let mk_opt = |t: Type| Type::new_sum([type_row![], [t].into()]);

        let cpy_to_qb = FnTransformer(|ct: &CustomType| (ct == &cpy).then_some(qb_t()));

        let mut t = mk_opt(cpy.clone().into());
        assert_eq!(t.transform(&cpy_to_qb), Ok(true));
        assert_eq!(t, mk_opt(qb_t()));

        let coln = e.get_type(&COLN).unwrap();
        let c_of_cpy = coln
            .instantiate([Term::new_list([Type::from(cpy.clone()).into()])])
            .unwrap();

        let mut t = Type::new_extension(c_of_cpy.clone());
        assert_eq!(
            t.transform(&cpy_to_qb),
            Err(SignatureError::from(TermTypeError::TypeMismatch {
                type_: Box::new(TypeBound::Copyable.into()),
                term: Box::new(qb_t().into())
            }))
        );

        let mut t = Type::new_extension(
            coln.instantiate([Term::new_list([mk_opt(Type::from(cpy.clone())).into()])])
                .unwrap(),
        );
        assert_eq!(
            t.transform(&cpy_to_qb),
            Err(SignatureError::from(TermTypeError::TypeMismatch {
                type_: Box::new(TypeBound::Copyable.into()),
                term: Box::new(mk_opt(qb_t()).into())
            }))
        );

        // Finally, check handling Coln<Cpy> overrides handling of Cpy
        let cpy_to_qb2 = FnTransformer(|ct: &CustomType| {
            assert_ne!(ct, &cpy);
            (ct == &c_of_cpy).then_some(usize_t())
        });
        let mut t = Type::new_extension(
            coln.instantiate([Term::new_list(vec![Type::from(c_of_cpy.clone()).into(); 2])])
                .unwrap(),
        );
        assert_eq!(t.transform(&cpy_to_qb2), Ok(true));
        assert_eq!(
            t,
            Type::new_extension(
                coln.instantiate([Term::new_list([usize_t().into(), usize_t().into()])])
                    .unwrap()
            )
        );
    }

    mod proptest {

        use crate::proptest::RecursionDepth;

        use crate::types::{CustomType, FuncValueType, SumType, Type, TypeBound, TypeRow};
        use proptest::{prelude::*, strategy::Union};

        impl Arbitrary for SumType {
            type Parameters = RecursionDepth;
            type Strategy = BoxedStrategy<Self>;
            fn arbitrary_with(depth: Self::Parameters) -> Self::Strategy {
                use proptest::collection::vec;
                if depth.leaf() {
                    any::<u8>().prop_map(Self::new_unary).boxed()
                } else {
                    vec(any_with::<TypeRow>(depth), 0..3)
                        .prop_map(SumType::new)
                        .boxed()
                }
            }
        }

        impl Arbitrary for Type {
            type Parameters = RecursionDepth;
            type Strategy = BoxedStrategy<Self>;
            fn arbitrary_with(depth: Self::Parameters) -> Self::Strategy {
                let strat = Union::new([
                    (any::<usize>(), any::<TypeBound>())
                        .prop_map(|(i, b)| Type::new_var_use(i, b))
                        .boxed(),
                    any_with::<CustomType>(depth.into())
                        .prop_map(Type::new_extension)
                        .boxed(),
                ]);
                if depth.leaf() {
                    return strat.boxed();
                }
                let depth = depth.descend();
                strat
                    .or(any_with::<FuncValueType>(depth)
                        .prop_map(Type::new_function)
                        .boxed())
                    .or(any_with::<SumType>(depth).prop_map(Type::from).boxed())
                    .boxed()
            }
        }
    }
}

#[cfg(test)]
pub(super) mod proptest_utils {
    use proptest::collection::vec;
    use proptest::prelude::{Strategy, any_with};

    use crate::proptest::RecursionDepth;

    use super::serialize::{ArrayOrTermSer, TermSer, TypeArgSer, TypeParamSer};
    use super::type_param::Term;

    fn term_is_serde_type_arg(t: &Term) -> bool {
        let TermSer::TypeArg(arg) = TermSer::from(t.clone()) else {
            return false;
        };
        match arg {
            TypeArgSer::List { elems: terms }
            | TypeArgSer::ListConcat { lists: terms }
            | TypeArgSer::Tuple { elems: terms }
            | TypeArgSer::TupleConcat { tuples: terms } => terms.iter().all(term_is_serde_type_arg),
            TypeArgSer::Variable { v } => term_is_serde_type_param(&v.cached_decl),
            TypeArgSer::Type { ty } => match Term::from(ty) {
                Term::RuntimeExtension(cty) => cty.args().iter().all(term_is_serde_type_arg),
                // Do we need to inspect inside function types? sum types?
                _ => true,
            },
            TypeArgSer::BoundedNat { .. }
            | TypeArgSer::String { .. }
            | TypeArgSer::Bytes { .. }
            | TypeArgSer::Float { .. } => true,
        }
    }

    fn term_is_serde_type_param(t: &Term) -> bool {
        let TermSer::TypeParam(parm) = TermSer::from(t.clone()) else {
            return false;
        };
        match parm {
            TypeParamSer::Type { .. }
            | TypeParamSer::BoundedNat { .. }
            | TypeParamSer::String
            | TypeParamSer::Bytes
            | TypeParamSer::Float
            | TypeParamSer::StaticType
            | TypeParamSer::ConstType { .. } => true,
            TypeParamSer::List { param } => term_is_serde_type_param(&param),
            TypeParamSer::Tuple { params } => {
                match &params {
                    ArrayOrTermSer::Array(terms) => terms.iter().all(term_is_serde_type_param),
                    ArrayOrTermSer::Term(b) => match &**b {
                        Term::List(_) => panic!("Should be represented as ArrayOrTermSer::Array"),
                        // This might be well-typed, but does not fit the (TODO: update) JSON schema
                        Term::Variable(_) => false,
                        // Similarly, but not produced by our `impl Arbitrary`:
                        Term::ListConcat(_) => todo!("Update schema"),

                        // The others do not fit the JSON schema, and are not well-typed,
                        // but can be produced by our impl of Arbitrary, so we must filter out:
                        _ => false,
                    },
                }
            }
        }
    }

    pub fn any_serde_type_arg(depth: RecursionDepth) -> impl Strategy<Value = Term> {
        any_with::<Term>(depth).prop_filter("Term was not a TypeArg", term_is_serde_type_arg)
    }

    pub fn any_serde_type_arg_vec() -> impl Strategy<Value = Vec<Term>> {
        vec(any_serde_type_arg(RecursionDepth::default()), 1..3)
    }

    pub fn any_serde_type_param(depth: RecursionDepth) -> impl Strategy<Value = Term> {
        any_with::<Term>(depth).prop_filter("Term was not a TypeParam", term_is_serde_type_param)
    }
}
