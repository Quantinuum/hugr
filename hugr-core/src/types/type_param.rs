//! Type Parameters
//!
//! Parameters for [`TypeDef`]s provided by extensions
//!
//! [`TypeDef`]: crate::extension::TypeDef

use itertools::Itertools as _;
use ordered_float::OrderedFloat;
#[cfg(test)]
use proptest_derive::Arbitrary;
use smallvec::{SmallVec, smallvec};
use std::iter::FusedIterator;
use std::num::NonZeroU64;
use std::sync::Arc;
use thiserror::Error;
use tracing::warn;

use super::{Substitution, Transformable, Type, TypeBound, TypeRowLike, TypeTransformer};
use crate::extension::SignatureError;
use crate::types::{CustomType, FuncValueType, GeneralSum, SumType};

/// The upper non-inclusive bound of a [`TypeParam::BoundedNat`]
// A None inner value implies the maximum bound: u64::MAX + 1 (all u64 values valid)
#[derive(
    Clone, Debug, PartialEq, Eq, Hash, derive_more::Display, serde::Deserialize, serde::Serialize,
)]
#[display("{}", _0.map(|i|i.to_string()).unwrap_or("-".to_string()))]
#[cfg_attr(test, derive(Arbitrary))]
pub struct UpperBound(Option<NonZeroU64>);
impl UpperBound {
    fn valid_value(&self, val: u64) -> bool {
        match (val, self.0) {
            (0, _) | (_, None) => true,
            (val, Some(inner)) if NonZeroU64::new(val).unwrap() < inner => true,
            _ => false,
        }
    }
    fn contains(&self, other: &UpperBound) -> bool {
        match (self.0, other.0) {
            (None, _) => true,
            (Some(b1), Some(b2)) if b1 >= b2 => true,
            _ => false,
        }
    }

    /// Returns the value of the upper bound.
    #[must_use]
    pub fn value(&self) -> &Option<NonZeroU64> {
        &self.0
    }
}

/// A [`Term`] that is a static argument to an operation or constructor.
pub type TypeArg = Term;

/// A [`Term`] that is the static kind of an operation or constructor parameter.
pub type TypeParam = Term;

/// The main entity in the static language (aka "type system") of Hugr.
///
/// Terms include types (i.e. which describe sets of runtime values)
/// but also other compile-time entities which can be used to parametrize
/// and instantiate functions, ops, and types. (For example, array lengths
/// are not types but they are static parameters of array types and ops.)
///
/// Terms are used for both parameter declarations and arguments fitting those
/// parameters, e.g. a [Term::FloatKind] parameter would be instantiated (statically)
/// with a [Term::Float] argument. [`check_term_kind`] checks that an argument
/// is valid (of the correct kind) for the parameter.
// TODO it might be good to have a separate function that tells, for a given Term,
// whether it is a kind (for which there is *any* valid argument); we could then
// rule out using as parameters any Term which is not a kind.
#[derive(
    Clone, Debug, PartialEq, Eq, Hash, derive_more::Display, serde::Deserialize, serde::Serialize,
)]
#[non_exhaustive]
#[serde(
    from = "crate::types::serialize::TermSer",
    into = "crate::types::serialize::TermSer"
)]
pub enum Term {
    /// The kind of runtime types.
    #[display("Type{}", match _0 {
        TypeBound::Linear => String::new(),
        _ => format!("[{_0}]")
    })]
    TypeKind(TypeBound),
    /// The kind of static data.
    StaticKind,
    /// The kind of static natural numbers up to a given bound.
    #[display("{}", match _0.value() {
        Some(v) => format!("BoundedNat[{v}]"),
        None => "Nat".to_string()
    })]
    BoundedNatKind(UpperBound),
    /// The kind of static strings. See [`Term::String`].
    StringKind,
    /// The kind of static byte strings. See [`Term::Bytes`].
    BytesKind,
    /// The kind of static floating point numbers. See [`Term::Float`].
    FloatKind,
    /// The kind of static lists of indeterminate size, each of whose elements
    /// is a `Term` of the specified kind
    #[display("ListType[{_0}]")]
    ListKind(Box<Term>),
    /// The kind of static tuples.
    #[display("TupleType[{_0}]")]
    TupleKind(Box<Term>),
    /// The type of runtime values defined by an extension type.
    /// Instance of [Self::TypeKind] for some bound.
    //
    // TODO optimise with `Box<CustomType>`?
    // or some static version of this?
    #[display("{_0}")]
    ExtensionType(CustomType),
    /// The type of runtime values that are function pointers.
    /// Instance of [Self::TypeKind]`(`[TypeBound::Copyable]`)`.
    /// Function values may be passed around without knowing their arity
    /// (i.e. with row vars) as long as they are not called.
    #[display("{_0}")]
    FunctionType(Box<FuncValueType>),
    /// The type of runtime values that are sums of products (ADTs)
    /// Instance of [Self::TypeKind]`(bound)` for `bound` calculated from each variant's elements.
    #[display("{_0}")]
    SumType(SumType),
    /// A 64bit unsigned integer literal. Instance of [`Term::BoundedNatKind`].
    #[display("{_0}")]
    BoundedNat(u64),
    /// UTF-8 encoded string literal. Instance of [`Term::StringKind`].
    #[display("\"{_0}\"")]
    String(String),
    /// Byte string literal. Instance of [`Term::BytesKind`].
    #[display("bytes")]
    Bytes(Arc<[u8]>),
    /// A 64-bit floating point number. Instance of [`Term::FloatKind`].
    #[display("{}", _0.into_inner())]
    Float(OrderedFloat<f64>),
    /// A list of static terms. Instance of [`Term::Listiund`].
    #[display("[{}]", _0.iter().map(|t|t.to_string()).join(", "))]
    List(Vec<Term>),
    /// Instance of [`TypeParam::ListKind`] defined by a sequence of concatenated lists of the same type.
    #[display("[{}]", {
        use itertools::Itertools as _;
        _0.iter().map(|t| format!("... {t}")).join(",")
    })]
    ListConcat(Vec<TypeArg>),
    /// Instance of [`TypeParam::TupleKind`] defined by a sequence of elements of varying kind.
    #[display("({})", {
        use itertools::Itertools as _;
        _0.iter().map(std::string::ToString::to_string).join(",")
    })]
    Tuple(Vec<Term>),
    /// Instance of [`TypeParam::TupleKind`] defined by a sequence of concatenated tuples.
    #[display("({})", {
        use itertools::Itertools as _;
        _0.iter().map(|tuple| format!("... {tuple}")).join(",")
    })]
    TupleConcat(Vec<TypeArg>),
    /// Variable (used in type schemes or inside polymorphic functions),
    /// but not a runtime type (not even a row variable i.e. list of runtime types)
    /// - see [`Term::new_var_use`]
    #[display("{_0}")]
    Variable(TermVar),

    /// The kind of constants for a runtime type.
    ///
    /// A constant is a compile time description of how to produce a runtime value.
    /// The runtime value is constructed when the constant is loaded.
    ///
    /// Constants are distinct from the runtime values that they describe. In
    /// particular, as part of the term language, constants can be freely copied
    /// or destroyed even when they describe a non-linear runtime value.
    ConstKind(Box<Type>),
}

impl Term {
    /// An empty list of Terms.
    pub const EMPTY_LIST: Self = Self::List(vec![]);

    /// Creates a [`Term::BoundedNatKind`] with the maximum bound (`u64::MAX` + 1).
    #[must_use]
    pub const fn max_nat_kind() -> Self {
        Self::BoundedNatKind(UpperBound(None))
    }

    /// Creates a [`Term::BoundedNatKind`] with the stated upper bound (non-exclusive).
    #[must_use]
    pub const fn bounded_nat_kind(upper_bound: NonZeroU64) -> Self {
        Self::BoundedNatKind(UpperBound(Some(upper_bound)))
    }

    /// Creates a new [`Term::List`] given a sequence of its items.
    pub fn new_list<T: Into<Term>>(items: impl IntoIterator<Item = T>) -> Self {
        Self::List(items.into_iter().map_into().collect())
    }

    /// Creates a new [`Term::ListKind`] given the type of its elements.
    pub fn new_list_kind(elem: impl Into<Term>) -> Self {
        Self::ListKind(Box::new(elem.into()))
    }

    /// Creates a new [`Term::TupleKind`] given the type of its elements.
    pub fn new_tuple_kind(item_types: impl Into<Term>) -> Self {
        Self::TupleKind(Box::new(item_types.into()))
    }

    /// Creates a new [`Term::ConstKind`] from a runtime type.
    pub fn new_const(ty: impl Into<Type>) -> Self {
        Self::ConstKind(Box::new(ty.into()))
    }

    /// Checks if this term is a supertype of another.
    ///
    /// The subtyping relation applies primarily to terms that represent static
    /// types. For consistency the relation is extended to a partial order on
    /// all terms; in particular it is reflexive so that every term (even if it
    /// is not a static type) is considered a subtype of itself.
    fn is_supertype(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::TypeKind(b1), Term::TypeKind(b2)) => b1.contains(*b2),
            (Term::BoundedNatKind(b1), Term::BoundedNatKind(b2)) => b1.contains(b2),
            (Term::StringKind, Term::StringKind) => true,
            (Term::StaticKind, Term::StaticKind) => true,
            (Term::ListKind(e1), Term::ListKind(e2)) => e1.is_supertype(e2),
            // The term inside a TupleType is a list of types, so this is ok as long as
            // supertype holds element-wise
            (Term::TupleKind(es1), Term::TupleKind(es2)) => es1.is_supertype(es2),
            (Term::BytesKind, Term::BytesKind) => true,
            (Term::FloatKind, Term::FloatKind) => true,
            // Needed for TupleType, does not make a great deal of sense otherwise:
            (Term::List(es1), Term::List(es2)) => {
                es1.len() == es2.len() && es1.iter().zip(es2).all(|(e1, e2)| e1.is_supertype(e2))
            }
            // The following are not types (they have no instances), so these are just to
            // maintain reflexivity of the relation:
            (Term::SumType(t1), Term::SumType(t2)) => t1 == t2,
            (Term::FunctionType(f1), Term::FunctionType(f2)) => f1 == f2,
            (Term::ExtensionType(c1), Term::ExtensionType(c2)) => c1 == c2,
            (Term::BoundedNat(n1), Term::BoundedNat(n2)) => n1 == n2,
            (Term::String(s1), Term::String(s2)) => s1 == s2,
            (Term::Bytes(v1), Term::Bytes(v2)) => v1 == v2,
            (Term::Float(f1), Term::Float(f2)) => f1 == f2,
            (Term::Variable(v1), Term::Variable(v2)) => v1 == v2,
            (Term::Tuple(es1), Term::Tuple(es2)) => {
                es1.len() == es2.len() && es1.iter().zip(es2).all(|(e1, e2)| e1.is_supertype(e2))
            }
            _ => false,
        }
    }

    /// Returns true if this term is an empty list (contains no elements)
    pub(super) fn is_empty_list(&self) -> bool {
        match self {
            Term::List(v) => v.is_empty(),
            // We probably don't need to be this thorough in dealing with unnormalized forms but it's easy enough
            Term::ListConcat(v) => v.iter().all(Term::is_empty_list),
            _ => false,
        }
    }

    /// Returns the inner [`CustomType`] if this `Term` is a [Self::ExtensionType]
    pub fn as_extension(&self) -> Option<&CustomType> {
        match self {
            Term::ExtensionType(ct) => Some(ct),
            _ => None,
        }
    }

    /// Returns the inner [`SumType`] if this `Term` is a [Self::SumType].
    pub fn as_sum(&self) -> Option<&SumType> {
        match self {
            Term::SumType(s) => Some(s),
            _ => None,
        }
    }
}

impl From<TypeBound> for Term {
    fn from(bound: TypeBound) -> Self {
        Self::TypeKind(bound)
    }
}

impl From<UpperBound> for Term {
    fn from(bound: UpperBound) -> Self {
        Self::BoundedNatKind(bound)
    }
}

impl From<u64> for Term {
    fn from(n: u64) -> Self {
        Self::BoundedNat(n)
    }
}

impl From<String> for Term {
    fn from(arg: String) -> Self {
        Term::String(arg)
    }
}

impl From<&str> for Term {
    fn from(arg: &str) -> Self {
        Term::String(arg.to_string())
    }
}

impl From<Vec<Term>> for Term {
    fn from(elems: Vec<Term>) -> Self {
        Self::new_list(elems)
    }
}

impl<const N: usize> From<[Term; N]> for Term {
    fn from(value: [Term; N]) -> Self {
        Self::new_list(value)
    }
}

/// Variable in a [`Term`], i.e. contents of a [`Term::Variable`].
#[derive(
    Clone, Debug, PartialEq, Eq, Hash, serde::Deserialize, serde::Serialize, derive_more::Display,
)]
#[display("#{idx}")]
pub struct TermVar {
    idx: usize,
    pub(in crate::types) cached_decl: Box<Term>,
}

impl Term {
    /// Makes a `TypeArg` representing a use (occurrence) of the type variable
    /// with the specified index.
    ///
    /// `decl` must be exactly that with which the variable was declared.
    #[must_use]
    pub fn new_var_use(idx: usize, decl: impl Into<Term>) -> Self {
        Term::Variable(TermVar {
            idx,
            cached_decl: Box::new(decl.into()),
        })
    }

    /// Makes a `Term` representing a use (occurrence) of a variable whose
    /// kind is a [Term::ListKind] of [Term::TypeKind].
    #[must_use]
    pub fn new_row_var_use(idx: usize, b: TypeBound) -> Self {
        Self::new_var_use(idx, Term::new_list_kind(b))
    }

    /// Creates a new string literal.
    #[inline]
    pub fn new_string(str: impl ToString) -> Self {
        Self::String(str.to_string())
    }

    /// Creates or returns a term equivalent to concatenating a number of lists.
    ///
    /// If there is only one list, returns it directly.
    #[inline]
    pub fn concat_lists(lists: impl IntoIterator<Item = Self>) -> Self {
        match lists.into_iter().exactly_one() {
            Ok(list) => list,
            Err(e) => Self::ListConcat(e.collect()),
        }
    }

    /// Creates a new tuple from its items.
    #[inline]
    pub fn new_tuple(items: impl IntoIterator<Item = Self>) -> Self {
        Self::Tuple(items.into_iter().collect())
    }

    /// Creates a new concatenated tuple.
    #[inline]
    pub fn new_tuple_concat(tuples: impl IntoIterator<Item = Self>) -> Self {
        Self::TupleConcat(tuples.into_iter().collect())
    }

    /// Returns an integer if the [`Term`] is a natural number literal.
    #[must_use]
    pub fn as_nat(&self) -> Option<u64> {
        match self {
            TypeArg::BoundedNat(n) => Some(*n),
            _ => None,
        }
    }

    pub(crate) const fn least_upper_bound(&self) -> Option<TypeBound> {
        match self {
            Self::ExtensionType(ct) => Some(ct.bound()),
            Self::SumType(st) => Some(st.bound()),
            Self::FunctionType(_) => Some(TypeBound::Copyable),
            Self::Variable(v) => match &*v.cached_decl {
                TypeParam::TypeKind(b) => Some(*b),
                _ => None,
            },
            _ => None,
        }
    }

    /// Report if this is a copyable runtime type, i.e. an instance
    /// of [Self::TypeKind]`(`[TypeBound::Copyable]`)`
    // where the least upper bound of the type is contained by the copyable bound.
    pub(crate) fn copyable(&self) -> bool {
        self.least_upper_bound()
            .is_some_and(|b| TypeBound::Copyable.contains(b))
    }

    /// Report if this is a runtime type, i.e. an instance of [Self::TypeKind] for some bound.
    ///
    /// If so, [Type::try_from(Type)] will succeed and can be followed by [Type::least_upper_bound] to get the bound.
    pub fn is_runtime_type(&self) -> bool {
        self.least_upper_bound().is_some()
    }

    /// Returns a string if the [`Term`] is a string literal.
    #[must_use]
    pub fn as_string(&self) -> Option<String> {
        match self {
            TypeArg::String(arg) => Some(arg.clone()),
            _ => None,
        }
    }

    /// Checks variables are as declared and [CustomType] arguments fit their parameters.
    /// Does not check that e.g. list elements all have same type (except inside a
    /// [CustomType] where we know the element type from the corresponding list parameter)
    /// - this is left to [check_term_kind].
    pub(crate) fn validate(&self, var_decls: &[TypeParam]) -> Result<(), SignatureError> {
        match self {
            Term::SumType(SumType::General(GeneralSum { rows, bound })) => {
                rows.iter().try_for_each(|row| row.validate(var_decls))?;
                debug_assert!(
                    bound == &TypeBound::Linear
                        || rows.iter().all(|row| check_term_kind(
                            row,
                            &Term::new_list_kind(*bound)
                        )
                        .is_ok())
                );
                Ok(())
            }
            Term::SumType(SumType::Unit { .. }) => Ok(()), // No leaves there
            Term::ExtensionType(custy) => custy.validate(var_decls),
            Term::FunctionType(ft) => ft.validate(var_decls),
            Term::List(elems) => elems.iter().try_for_each(|a| a.validate(var_decls)),
            Term::Tuple(elems) => elems.iter().try_for_each(|a| a.validate(var_decls)),
            Term::BoundedNat(_) | Term::String { .. } | Term::Float(_) | Term::Bytes(_) => Ok(()),
            TypeArg::ListConcat(lists) => lists.iter().try_for_each(|a| a.validate(var_decls)),
            TypeArg::TupleConcat(tuples) => tuples.iter().try_for_each(|a| a.validate(var_decls)),
            Term::Variable(tv) => tv.check_decl(var_decls),
            Term::TypeKind { .. } => Ok(()),
            Term::BoundedNatKind { .. } => Ok(()),
            Term::StringKind => Ok(()),
            Term::BytesKind => Ok(()),
            Term::FloatKind => Ok(()),
            Term::ListKind(item_type) => item_type.validate(var_decls),
            Term::TupleKind(item_types) => item_types.validate(var_decls),
            Term::StaticKind => Ok(()),
            Term::ConstKind(ty) => ty.validate(var_decls),
        }
    }

    pub(crate) fn substitute(&self, t: &Substitution) -> Self {
        match self {
            TypeArg::SumType(SumType::Unit { .. }) => self.clone(),
            TypeArg::SumType(SumType::General(GeneralSum { rows, .. })) => {
                // A substitution of a row variable for an empty list,
                // could make the general case into a unary SumType.
                Term::SumType(SumType::new(rows.iter().map(|r| r.substitute(t))))
            }
            TypeArg::ExtensionType(cty) => Term::ExtensionType(cty.substitute(t)),
            TypeArg::FunctionType(bf) => Term::FunctionType(Box::new(bf.substitute(t))),

            TypeArg::BoundedNat(_) | TypeArg::String(_) | TypeArg::Bytes(_) | TypeArg::Float(_) => {
                self.clone()
            } // We do not allow variables as bounds on BoundedNat's
            TypeArg::List(elems) => Self::List(elems.iter().map(|e| e.substitute(t)).collect()),
            TypeArg::ListConcat(lists) => {
                // When a substitution instantiates spliced list variables, we
                // may be able to merge the concatenated lists.
                Self::new_list_from_parts(
                    lists.iter().map(|list| SeqPart::Splice(list.substitute(t))),
                )
            }
            Term::Tuple(elems) => {
                Term::Tuple(elems.iter().map(|elem| elem.substitute(t)).collect())
            }
            TypeArg::TupleConcat(tuples) => {
                // When a substitution instantiates spliced tuple variables,
                // we may be able to merge the concatenated tuples.
                Self::new_tuple_from_parts(
                    tuples
                        .iter()
                        .map(|tuple| SeqPart::Splice(tuple.substitute(t))),
                )
            }
            TypeArg::Variable(TermVar { idx, cached_decl }) => t.apply_var(*idx, cached_decl),
            Term::TypeKind(_) => self.clone(),
            Term::BoundedNatKind(_) => self.clone(),
            Term::StringKind => self.clone(),
            Term::BytesKind => self.clone(),
            Term::FloatKind => self.clone(),
            Term::ListKind(item_type) => Term::new_list_kind(item_type.substitute(t)),
            Term::TupleKind(item_types) => Term::new_tuple_kind(item_types.substitute(t)),
            Term::StaticKind => self.clone(),
            Term::ConstKind(ty) => Term::new_const(ty.substitute(t)),
        }
    }

    /// Helper method for [`TypeArg::new_list_from_parts`] and [`TypeArg::new_tuple_from_parts`].
    fn new_seq_from_parts(
        parts: impl IntoIterator<Item = SeqPart<Self>>,
        make_items: impl Fn(Vec<Self>) -> Self,
        make_concat: impl Fn(Vec<Self>) -> Self,
    ) -> Self {
        let mut items = Vec::new();
        let mut seqs = Vec::new();

        for part in parts {
            match part {
                SeqPart::Item(item) => items.push(item),
                SeqPart::Splice(seq) => {
                    if !items.is_empty() {
                        seqs.push(make_items(std::mem::take(&mut items)));
                    }
                    seqs.push(seq);
                }
            }
        }

        if seqs.is_empty() {
            make_items(items)
        } else if items.is_empty() {
            make_concat(seqs)
        } else {
            seqs.push(make_items(items));
            make_concat(seqs)
        }
    }

    /// Creates a new list from a sequence of [`SeqPart`]s.
    pub fn new_list_from_parts(parts: impl IntoIterator<Item = SeqPart<Self>>) -> Self {
        Self::new_seq_from_parts(
            parts.into_iter().flat_map(ListPartIter::new),
            TypeArg::List,
            TypeArg::concat_lists,
        )
    }

    /// Iterates over the [`SeqPart`]s of a list.
    ///
    /// # Examples
    ///
    /// The parts of a closed list are the items of that list wrapped in [`SeqPart::Item`]:
    ///
    /// ```
    /// # use hugr_core::types::type_param::{Term, SeqPart};
    /// # let a = Term::new_string("a");
    /// # let b = Term::new_string("b");
    /// let term = Term::new_list([a.clone(), b.clone()]);
    ///
    /// assert_eq!(
    ///     term.into_list_parts().collect::<Vec<_>>(),
    ///     vec![SeqPart::Item(a), SeqPart::Item(b)]
    /// );
    /// ```
    ///
    /// Parts of a concatenated list that are not closed lists are wrapped in [`SeqPart::Splice`]:
    ///
    /// ```
    /// # use hugr_core::types::type_param::{Term, SeqPart};
    /// # let a = Term::new_string("a");
    /// # let b = Term::new_string("b");
    /// # let c = Term::new_string("c");
    /// let var = Term::new_var_use(0, Term::new_list_kind(Term::StringKind));
    /// let term = Term::concat_lists([
    ///     Term::new_list([a.clone(), b.clone()]),
    ///     var.clone(),
    ///     Term::new_list([c.clone()])
    ///  ]);
    ///
    /// assert_eq!(
    ///     term.into_list_parts().collect::<Vec<_>>(),
    ///     vec![SeqPart::Item(a), SeqPart::Item(b), SeqPart::Splice(var), SeqPart::Item(c)]
    /// );
    /// ```
    ///
    /// Nested concatenations are traversed recursively:
    ///
    /// ```
    /// # use hugr_core::types::type_param::{Term, SeqPart};
    /// # let a = Term::new_string("a");
    /// # let b = Term::new_string("b");
    /// # let c = Term::new_string("c");
    /// let term = Term::concat_lists([
    ///     Term::concat_lists([
    ///         Term::new_list([a.clone()]),
    ///         Term::new_list([b.clone()])
    ///     ]),
    ///     Term::EMPTY_LIST,
    ///     Term::new_list([c.clone()])
    /// ]);
    ///
    /// assert_eq!(
    ///     term.into_list_parts().collect::<Vec<_>>(),
    ///     vec![SeqPart::Item(a), SeqPart::Item(b), SeqPart::Item(c)]
    /// );
    /// ```
    ///
    /// When invoked on a type argument that is not a list, a single
    /// [`SeqPart::Splice`] is returned that wraps the type argument.
    /// This is the expected behaviour for type variables that stand for lists.
    /// This behaviour also allows this method not to fail on ill-typed type arguments.
    /// ```
    /// # use hugr_core::types::type_param::{Term, SeqPart};
    /// let term = Term::new_string("not a list");
    /// assert_eq!(
    ///     term.clone().into_list_parts().collect::<Vec<_>>(),
    ///     vec![SeqPart::Splice(term)]
    /// );
    /// ```
    #[inline]
    pub fn into_list_parts(self) -> impl Iterator<Item = SeqPart<Self>> {
        ListPartIter::new(SeqPart::Splice(self))
    }

    /// Creates a new tuple from a sequence of [`SeqPart`]s.
    ///
    /// Analogous to [`TypeArg::new_list_from_parts`].
    pub fn new_tuple_from_parts(parts: impl IntoIterator<Item = SeqPart<Self>>) -> Self {
        Self::new_seq_from_parts(
            parts.into_iter().flat_map(TuplePartIter::new),
            TypeArg::Tuple,
            TypeArg::TupleConcat,
        )
    }

    /// Iterates over the [`SeqPart`]s of a tuple.
    ///
    /// Analogous to [`TypeArg::into_list_parts`].
    #[inline]
    pub fn into_tuple_parts(self) -> impl Iterator<Item = SeqPart<Self>> {
        TuplePartIter::new(SeqPart::Splice(self))
    }
}

impl Transformable for Term {
    fn transform<T: TypeTransformer>(&mut self, tr: &T) -> Result<bool, T::Err> {
        match self {
            Term::ExtensionType(custom_type) => {
                if let Some(nt) = tr.apply_custom(custom_type)? {
                    *self = nt.0;
                    Ok(true)
                } else {
                    let args_changed = custom_type.args_mut().transform(tr)?;
                    if args_changed {
                        *custom_type = custom_type
                            .get_type_def(&custom_type.get_extension()?)?
                            .instantiate(custom_type.args())?;
                    }
                    Ok(args_changed)
                }
            }
            Term::FunctionType(fty) => fty.transform(tr),
            Term::SumType(sum_type) => sum_type.transform(tr),
            Term::List(elems) => elems.transform(tr),
            Term::Tuple(elems) => elems.transform(tr),
            Term::BoundedNat(_)
            | Term::String(_)
            | Term::Variable(_)
            | Term::Float(_)
            | Term::Bytes(_) => Ok(false),
            Term::TypeKind { .. } => Ok(false),
            Term::BoundedNatKind { .. } => Ok(false),
            Term::StringKind => Ok(false),
            Term::BytesKind => Ok(false),
            Term::FloatKind => Ok(false),
            Term::ListKind(item_type) => item_type.transform(tr),
            Term::TupleKind(item_types) => item_types.transform(tr),
            Term::StaticKind => Ok(false),
            TypeArg::ListConcat(lists) => lists.transform(tr),
            TypeArg::TupleConcat(tuples) => tuples.transform(tr),
            Term::ConstKind(ty) => ty.transform(tr),
        }
    }
}

impl TermVar {
    /// Return the index.
    #[must_use]
    pub fn index(&self) -> usize {
        self.idx
    }

    /// Determines whether this represents a row variable; if so, returns
    /// the [`TypeBound`] of the individual types it might stand for.
    #[must_use]
    pub fn bound_if_row_var(&self) -> Option<TypeBound> {
        if let Term::ListKind(item_type) = &*self.cached_decl
            && let Term::TypeKind(b) = **item_type
        {
            return Some(b);
        }
        None
    }

    /// Check that the cached declaration of this variable matches the actual one (provided).
    ///
    /// The cache just mirrors the declaration; the typevar can be used anywhere expecting
    /// a kind containing the decl - see [check_term_kind] / [Term::is_supertype].
    fn check_decl(&self, decls: &[TypeParam]) -> Result<(), SignatureError> {
        let idx = self.idx;
        let cached_decl: &TypeParam = &self.cached_decl;
        match decls.get(idx) {
            None => Err(SignatureError::FreeTypeVar {
                idx,
                num_decls: decls.len(),
            }),
            Some(actual) => {
                if actual == cached_decl {
                    Ok(())
                } else {
                    Err(SignatureError::TypeVarDoesNotMatchDeclaration {
                        cached: Box::new(cached_decl.clone()),
                        actual: Box::new(actual.clone()),
                    })
                }
            }
        }
    }
}

/// Checks that a [`Term`] (value) is a valid instance of another [`Term`] (kind)
///
/// I.e. the former is acceptable as an argument to a parameter of the latter.
pub fn check_term_kind(value: &Term, kind: &Term) -> Result<(), TermTypeError> {
    match (value, kind) {
        (Term::Variable(TermVar { cached_decl, .. }), _) if kind.is_supertype(cached_decl) => {
            Ok(())
        }
        (Term::SumType(st), Term::TypeKind(bound)) if bound.contains(st.bound()) => Ok(()),
        (Term::FunctionType(_), Term::TypeKind(_)) => Ok(()), // Function pointers are always Copyable so fit any bound
        (Term::ExtensionType(cty), Term::TypeKind(bound)) if bound.contains(cty.bound()) => Ok(()),
        (Term::List(elems), Term::ListKind(item_type)) => elems
            .iter()
            .try_for_each(|elem| check_term_kind(elem, item_type)),
        (Term::ListConcat(lists), Term::ListKind(_)) => lists
            .iter()
            .try_for_each(|list| check_term_kind(list, kind)),
        (TypeArg::Tuple(_) | TypeArg::TupleConcat(_), TypeParam::TupleKind(item_types)) => {
            let term_parts: Vec<_> = value.clone().into_tuple_parts().collect();
            let type_parts: Vec<_> = item_types.clone().into_list_parts().collect();

            for (term, type_) in term_parts.iter().zip(&type_parts) {
                match (term, type_) {
                    (SeqPart::Item(term), SeqPart::Item(type_)) => {
                        check_term_kind(term, type_)?;
                    }
                    (_, SeqPart::Splice(_)) | (SeqPart::Splice(_), _) => {
                        // TODO: Checking tuples with splicing requires more
                        // sophisticated validation infrastructure to do well.
                        warn!(
                            "Validation for open tuples is not implemented yet, succeeding regardless..."
                        );
                        return Ok(());
                    }
                }
            }

            if term_parts.len() != type_parts.len() {
                return Err(TermTypeError::WrongNumberTuple(
                    term_parts.len(),
                    type_parts.len(),
                ));
            }

            Ok(())
        }
        (Term::BoundedNat(val), Term::BoundedNatKind(bound)) if bound.valid_value(*val) => Ok(()),
        (Term::String { .. }, Term::StringKind) => Ok(()),
        (Term::Bytes(_), Term::BytesKind) => Ok(()),
        (Term::Float(_), Term::FloatKind) => Ok(()),

        // Static types
        (Term::StaticKind, Term::StaticKind) => Ok(()),
        (Term::StringKind, Term::StaticKind) => Ok(()),
        (Term::BytesKind, Term::StaticKind) => Ok(()),
        (Term::BoundedNatKind { .. }, Term::StaticKind) => Ok(()),
        (Term::FloatKind, Term::StaticKind) => Ok(()),
        (Term::ListKind { .. }, Term::StaticKind) => Ok(()),
        (Term::TupleKind(_), Term::StaticKind) => Ok(()),
        (Term::TypeKind(_), Term::StaticKind) => Ok(()),
        (Term::ConstKind(_), Term::StaticKind) => Ok(()),

        _ => Err(TermTypeError::TypeMismatch {
            term: Box::new(value.clone()),
            type_: Box::new(kind.clone()),
        }),
    }
}

/// Check a list of [`Term`]s is valid for a list of types.
pub fn check_term_kinds(terms: &[Term], types: &[Term]) -> Result<(), TermTypeError> {
    if terms.len() != types.len() {
        return Err(TermTypeError::WrongNumberArgs(terms.len(), types.len()));
    }
    for (term, type_) in terms.iter().zip(types.iter()) {
        check_term_kind(term, type_)?;
    }
    Ok(())
}

/// Errors that can occur when checking that a [`Term`] has an expected type.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum TermTypeError {
    #[allow(missing_docs)]
    /// For now, general case of a term not fitting a type.
    /// We'll have more cases when we allow general Containers.
    // TODO It may become possible to combine this with ConstTypeError.
    #[error("Term {term} does not fit declared type {type_}")]
    TypeMismatch { term: Box<Term>, type_: Box<Term> },
    /// Wrong number of type arguments (actual vs expected).
    // For now this only happens at the top level (TypeArgs of op/type vs TypeParams of Op/TypeDef).
    // However in the future it may be applicable to e.g. contents of Tuples too.
    #[error("Wrong number of type arguments: {0} vs expected {1} declared type parameters")]
    WrongNumberArgs(usize, usize),

    /// Wrong number of type arguments in tuple (actual vs expected).
    #[error(
        "Wrong number of type arguments to tuple parameter: {0} vs expected {1} declared type parameters"
    )]
    WrongNumberTuple(usize, usize),
    /// Opaque value type check error.
    #[error("Opaque type argument does not fit declared parameter type: {0}")]
    OpaqueTypeMismatch(#[from] crate::types::CustomCheckFailure),
    /// Invalid value
    #[error("Invalid value of type argument")]
    InvalidValue(Box<TypeArg>),
}

/// Part of a sequence.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SeqPart<T> {
    /// An individual item in the sequence.
    Item(T),
    /// A subsequence that is spliced into the parent sequence.
    Splice(T),
}

/// Iterator created by [`TypeArg::into_list_parts`].
#[derive(Debug, Clone)]
pub(crate) struct ListPartIter {
    parts: SmallVec<[SeqPart<TypeArg>; 1]>,
}

impl ListPartIter {
    #[inline]
    fn new(part: SeqPart<TypeArg>) -> Self {
        Self {
            parts: smallvec![part],
        }
    }
}

impl Iterator for ListPartIter {
    type Item = SeqPart<TypeArg>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.parts.pop()? {
                SeqPart::Splice(TypeArg::List(elems)) => self
                    .parts
                    .extend(elems.into_iter().rev().map(SeqPart::Item)),
                SeqPart::Splice(TypeArg::ListConcat(lists)) => self
                    .parts
                    .extend(lists.into_iter().rev().map(SeqPart::Splice)),
                part => return Some(part),
            }
        }
    }
}

impl FusedIterator for ListPartIter {}

/// Iterator created by [`TypeArg::into_tuple_parts`].
#[derive(Debug, Clone)]
pub(crate) struct TuplePartIter {
    parts: SmallVec<[SeqPart<TypeArg>; 1]>,
}

impl TuplePartIter {
    #[inline]
    fn new(part: SeqPart<TypeArg>) -> Self {
        Self {
            parts: smallvec![part],
        }
    }
}

impl Iterator for TuplePartIter {
    type Item = SeqPart<TypeArg>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.parts.pop()? {
                SeqPart::Splice(TypeArg::Tuple(elems)) => self
                    .parts
                    .extend(elems.into_iter().rev().map(SeqPart::Item)),
                SeqPart::Splice(TypeArg::TupleConcat(tuples)) => self
                    .parts
                    .extend(tuples.into_iter().rev().map(SeqPart::Splice)),
                part => return Some(part),
            }
        }
    }
}

impl FusedIterator for TuplePartIter {}

#[cfg(test)]
mod test {
    use super::{Substitution, TypeArg, TypeParam, check_term_kind};
    use crate::extension::prelude::{bool_t, usize_t};
    use crate::types::type_param::SeqPart;
    use crate::types::{Term, Type, TypeBound, TypeRow, type_param::TermTypeError};

    #[test]
    fn new_list_from_parts_items() {
        let a = TypeArg::new_string("a");
        let b = TypeArg::new_string("b");

        let parts = [SeqPart::Item(a.clone()), SeqPart::Item(b.clone())];
        let items = [a, b];

        assert_eq!(
            TypeArg::new_list_from_parts(parts.clone()),
            TypeArg::new_list(items.clone())
        );

        assert_eq!(
            TypeArg::new_tuple_from_parts(parts),
            TypeArg::new_tuple(items)
        );
    }

    #[test]
    fn new_list_from_parts_flatten() {
        let a = Term::new_string("a");
        let b = Term::new_string("b");
        let c = Term::new_string("c");
        let d = Term::new_string("d");
        let var = Term::new_var_use(0, Term::new_list_kind(Term::StringKind));
        let parts = [
            SeqPart::Splice(Term::new_list([a.clone(), b.clone()])),
            SeqPart::Splice(Term::concat_lists([Term::new_list([c.clone()])])),
            SeqPart::Item(d.clone()),
            SeqPart::Splice(var.clone()),
        ];
        assert_eq!(
            Term::new_list_from_parts(parts),
            Term::concat_lists([Term::new_list([a, b, c, d]), var])
        );
    }

    #[test]
    fn new_tuple_from_parts_flatten() {
        let a = Term::new_string("a");
        let b = Term::new_string("b");
        let c = Term::new_string("c");
        let d = Term::new_string("d");
        let var = Term::new_var_use(0, Term::new_tuple([Term::StringKind]));
        let parts = [
            SeqPart::Splice(Term::new_tuple([a.clone(), b.clone()])),
            SeqPart::Splice(Term::new_tuple_concat([Term::new_tuple([c.clone()])])),
            SeqPart::Item(d.clone()),
            SeqPart::Splice(var.clone()),
        ];
        assert_eq!(
            Term::new_tuple_from_parts(parts),
            Term::new_tuple_concat([Term::new_tuple([a, b, c, d]), var])
        );
    }

    #[test]
    fn type_arg_fits_param() {
        let rowvar = Term::new_row_var_use;
        fn check(arg: impl Into<TypeArg>, param: &TypeParam) -> Result<(), TermTypeError> {
            check_term_kind(&arg.into(), param)
        }
        fn check_seq<T: Clone + Into<TypeArg>>(
            args: &[T],
            param: &TypeParam,
        ) -> Result<(), TermTypeError> {
            check_term_kind(&Term::new_list(args.to_vec()), param)
        }
        // Simple cases: Term::XXXTypes are Term::TypeKind's
        check(usize_t(), &TypeBound::Copyable.into()).unwrap();
        let lst_of_cpy = TypeParam::new_list_kind(TypeBound::Copyable);
        check(usize_t(), &lst_of_cpy).unwrap_err();
        // ...but singleton sequences thereof are lists
        check_seq(&[usize_t()], &TypeBound::Linear.into()).unwrap_err();

        // Into a list of type, we can fit a single row var
        check(rowvar(0, TypeBound::Copyable), &lst_of_cpy).unwrap();
        // or a list of types, or a "concat" of row vars
        check(Term::new_list([usize_t()]), &lst_of_cpy).unwrap();
        check(
            Term::ListConcat(vec![rowvar(0, TypeBound::Copyable); 2]),
            &lst_of_cpy,
        )
        .unwrap();
        check(
            Term::concat_lists([
                rowvar(1, TypeBound::Linear),
                Term::new_list([usize_t()]),
                rowvar(0, TypeBound::Copyable),
            ]),
            &TypeParam::new_list_kind(TypeBound::Linear),
        )
        .unwrap();
        // but a *list* of the rowvar is a list of list of types, which is wrong
        check_seq(&[rowvar(0, TypeBound::Copyable)], &lst_of_cpy).unwrap_err();

        // Next one fails because a list of Copyable is required
        check(
            Term::concat_lists([
                rowvar(1, TypeBound::Linear),
                Term::new_list([usize_t()]),
                rowvar(0, TypeBound::Copyable),
            ]),
            &lst_of_cpy,
        )
        .unwrap_err();
        // seq of seq of types is not allowed
        check(
            vec![Term::from(usize_t()), Term::new_list([usize_t()])],
            &lst_of_cpy,
        )
        .unwrap_err();

        // Similar for nats (but no equivalent of fancy row vars)
        check(5, &TypeParam::max_nat_kind()).unwrap();
        check_seq(&[5], &TypeParam::max_nat_kind()).unwrap_err();
        let list_of_nat = TypeParam::new_list_kind(TypeParam::max_nat_kind());
        check(5, &list_of_nat).unwrap_err();
        check_seq(&[5], &list_of_nat).unwrap();
        check(TypeArg::new_var_use(0, list_of_nat.clone()), &list_of_nat).unwrap();
        // But no equivalent of row vars - can't append a nat onto a list-in-a-var:
        check(
            vec![5.into(), TypeArg::new_var_use(0, list_of_nat.clone())],
            &list_of_nat,
        )
        .unwrap_err();

        // `Term::TupleKind` requires a `Term::Tuple` of the same number of elems
        let usize_and_ty =
            TypeParam::new_tuple_kind([TypeParam::max_nat_kind(), Term::from(TypeBound::Copyable)]);
        check(
            TypeArg::Tuple(vec![5.into(), usize_t().into()]),
            &usize_and_ty,
        )
        .unwrap();
        check(
            TypeArg::Tuple(vec![usize_t().into(), 5.into()]),
            &usize_and_ty,
        )
        .unwrap_err(); // Wrong way around

        let two_types =
            Term::new_tuple_kind(Term::new_list([TypeBound::Linear, TypeBound::Linear]));
        check(TypeArg::new_var_use(0, two_types.clone()), &two_types).unwrap();
        // not a Row Var which could have any number of elems
        check(TypeArg::new_var_use(0, lst_of_cpy), &two_types).unwrap_err();
    }

    #[test]
    fn type_arg_subst_row() {
        let row_param = Term::new_list_kind(TypeBound::Copyable);
        let row_arg: Term = Term::new_list([bool_t(), Type::UNIT]);
        check_term_kind(&row_arg, &row_param).unwrap();

        // Now say a row variable referring to *that* row was used
        // to instantiate an outer "row parameter" (list of type).
        let outer_param = Term::new_list_kind(TypeBound::Linear);
        let outer_arg = Term::concat_lists([
            Term::new_row_var_use(0, TypeBound::Copyable),
            Term::new_list([usize_t()]),
        ]);
        check_term_kind(&outer_arg, &outer_param).unwrap();

        let outer_arg2 = outer_arg.substitute(&Substitution(&[row_arg]));
        assert_eq!(
            outer_arg2,
            Term::new_list([bool_t(), Type::UNIT, usize_t()])
        );

        // Of course this is still valid (as substitution is guaranteed to preserve validity)
        check_term_kind(&outer_arg2, &outer_param).unwrap();
    }

    #[test]
    fn subst_list_list() {
        let outer_param = Term::new_list_kind(Term::new_list_kind(TypeBound::Linear));
        let row_var_decl = Term::new_list_kind(TypeBound::Copyable);
        let row_var_use = Term::new_var_use(0, row_var_decl.clone());
        let good_arg = Term::new_list([
            // The row variables here refer to `row_var_decl` above
            Term::new_list([usize_t()]),
            row_var_use.clone(),
            Term::concat_lists([row_var_use, Term::new_list([usize_t()])]),
        ]);
        check_term_kind(&good_arg, &outer_param).unwrap();

        // Outer list cannot include single types:
        let Term::List(mut elems) = good_arg.clone() else {
            panic!()
        };
        let t: Term = usize_t().into();
        elems.push(t);
        assert_eq!(
            check_term_kind(&Term::new_list(elems), &outer_param),
            Err(TermTypeError::TypeMismatch {
                term: Box::new(usize_t().into()),
                // The error reports the type expected for each element of the list:
                type_: Box::new(TypeParam::new_list_kind(TypeBound::Linear))
            })
        );

        // Now substitute a list of two types for that row-variable
        let row_var_arg = Term::new_list([usize_t(), bool_t()]);
        check_term_kind(&row_var_arg, &row_var_decl).unwrap();
        let subst_arg = good_arg.substitute(&Substitution(std::slice::from_ref(&row_var_arg)));
        check_term_kind(&subst_arg, &outer_param).unwrap(); // invariance of substitution
        assert_eq!(
            subst_arg,
            Term::new_list([
                Term::new_list([usize_t()]),
                row_var_arg,
                Term::new_list([usize_t(), bool_t(), usize_t()])
            ])
        );
    }

    #[test]
    fn test_try_into_list_elements() {
        // Test successful conversion with List
        let types = vec![Type::new_unit_sum(1), bool_t()];
        let term = TypeArg::new_list(types.clone());
        let result = TypeRow::try_from(term);
        assert_eq!(result, Ok(TypeRow::from(types)));

        // Test failure with non-list
        let result = TypeRow::try_from(Term::from(Type::UNIT));
        assert!(result.is_err());
    }

    #[test]
    fn bytes_json_roundtrip() {
        let bytes_arg = Term::Bytes(vec![0, 1, 2, 3, 255, 254, 253, 252].into());
        let serialized = serde_json::to_string(&bytes_arg).unwrap();
        let deserialized: Term = serde_json::from_str(&serialized).unwrap();
        assert_eq!(deserialized, bytes_arg);
    }

    #[test]
    fn list_from_single_part_item() {
        // arbitrary, but not worth cost of trying everything in a proptest
        let term = Term::new_list([Term::new_string("foo")]);
        assert_eq!(
            Term::List(vec![term.clone()]),
            Term::new_list_from_parts(std::iter::once(SeqPart::Item(term)))
        );
    }

    #[test]
    fn list_from_single_part_splice() {
        // arbitrary, but not worth cost of trying everything in a proptest
        let term = Term::new_list([Term::new_string("foo")]);
        assert_eq!(
            term.clone(),
            Term::new_list_from_parts(std::iter::once(SeqPart::Splice(term)))
        );
    }

    #[test]
    fn list_concat_single_item() {
        // arbitrary, but not worth cost of trying everything in a proptest
        let term = Term::new_list([Term::new_string("foo")]);
        assert_eq!(term.clone(), Term::concat_lists([term]));
    }

    mod proptest {
        use prop::{collection::vec, strategy::Union};
        use proptest::prelude::*;

        use super::super::{TermVar, UpperBound};
        use crate::proptest::RecursionDepth;
        use crate::types::proptest_utils::any_serde_type_param;
        use crate::types::{Term, Type, TypeBound};

        impl Arbitrary for TermVar {
            type Parameters = RecursionDepth;
            type Strategy = BoxedStrategy<Self>;
            fn arbitrary_with(depth: Self::Parameters) -> Self::Strategy {
                (any::<usize>(), any_serde_type_param(depth))
                    .prop_map(|(idx, cached_decl)| Self {
                        idx,
                        cached_decl: Box::new(cached_decl),
                    })
                    .boxed()
            }
        }

        impl Arbitrary for Term {
            type Parameters = RecursionDepth;
            type Strategy = BoxedStrategy<Self>;
            fn arbitrary_with(depth: Self::Parameters) -> Self::Strategy {
                let strat = Union::new([
                    Just(Self::StringKind).boxed(),
                    Just(Self::BytesKind).boxed(),
                    Just(Self::FloatKind).boxed(),
                    Just(Self::StringKind).boxed(),
                    any::<TypeBound>().prop_map(Self::from).boxed(),
                    any::<UpperBound>().prop_map(Self::from).boxed(),
                    any::<u64>().prop_map(Self::from).boxed(),
                    any::<String>().prop_map(Self::from).boxed(),
                    any::<Vec<u8>>()
                        .prop_map(|bytes| Self::Bytes(bytes.into()))
                        .boxed(),
                    any::<f64>()
                        .prop_map(|value| Self::Float(value.into()))
                        .boxed(),
                    any_with::<Type>(depth).prop_map_into().boxed(),
                ]);
                if depth.leaf() {
                    return strat.boxed();
                }
                // we descend here because we these constructors contain Terms
                let depth = depth.descend();
                strat
                    .or(
                        // TODO this means we have two ways to create variables of type
                        // `TypeKind`, so we probably get more of them than we should`
                        any_with::<TermVar>(depth).prop_map(Self::Variable).boxed(),
                    )
                    .or(any_with::<Self>(depth)
                        .prop_map(Self::new_list_kind)
                        .boxed())
                    .or(any_with::<Self>(depth)
                        .prop_map(Self::new_tuple_kind)
                        .boxed())
                    .or(vec(any_with::<Self>(depth), 0..3)
                        .prop_map(Self::new_list)
                        .boxed())
                    .boxed()
            }
        }

        proptest! {
            #[test]
            fn term_contains_itself(term: Term) {
                assert!(term.is_supertype(&term));
            }
        }
    }
}
