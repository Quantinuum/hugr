//! Rows of types, used for function signatures,
//! designed to support efficient static allocation.

use std::{
    borrow::Cow,
    fmt::{self, Display, Write},
    ops::{Deref, DerefMut},
};

use super::{Substitution, Term, Transformable, Type, TypeTransformer, type_param::TypeParam};
use crate::{
    extension::SignatureError,
    types::{
        TypeBound,
        type_param::{TermTypeError, check_term_type},
    },
    utils::display_list,
};
use delegate::delegate;
use derive_more::Display;
use itertools::Itertools;

/// List of types, of known length, used for node signatures.
///
/// Also allows sharing via `Cow` and static allocation via [type_row!].
///
/// [type_row!]: crate::type_row
#[derive(Clone, PartialEq, Eq, Debug, Hash, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
#[serde(transparent)]
pub struct TypeRow {
    /// The datatypes in the row.
    types: Cow<'static, [Type]>,
}

impl Display for TypeRow {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_char('[')?;
        display_list(self.types.as_ref(), f)?;
        f.write_char(']')
    }
}

impl TypeRow {
    /// Create a new empty row.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            types: Cow::Owned(Vec::new()),
        }
    }

    /// Returns a new `TypeRow` with `xs` concatenated onto `self`.
    pub fn extend<'a>(&'a self, rest: impl IntoIterator<Item = &'a Type>) -> Self {
        self.iter().chain(rest).cloned().collect_vec().into()
    }

    /// Returns a reference to the types in the row.
    #[must_use]
    pub fn as_slice(&self) -> &[Type] {
        &self.types
    }

    delegate! {
        to self.types {
            /// Iterator over the types in the row.
            pub fn iter(&self) -> impl Iterator<Item = &Type>;

            /// Mutable vector of the types in the row.
            pub fn to_mut(&mut self) -> &mut Vec<Type>;

            /// Allow access (consumption) of the contained elements
            #[must_use] pub fn into_owned(self) -> Vec<Type>;

            /// Returns `true` if the row contains no types.
            #[must_use] pub fn is_empty(&self) -> bool;
        }
    }
}

/// Compared to just `pub(crate) trait`, this avoids a private_bounds
/// warning when the trait is used as a type bound on a public struct.
mod internal {
    use super::{SignatureError, Substitution, Transformable, TypeParam};

    /// Sub-trait of [`Transformable`] implemented by things that represent
    /// rows of types (fixed-length [`TypeRow`] or variable-length [`TypeRowRV`]).
    ///
    /// [`TypeRow`]: super::TypeRow
    /// [`TypeRowRV`]: super::TypeRowRV
    pub trait TypeRowLike: Transformable {
        /// Checks all variables used in `self` are in the provided list of bound
        /// variables, and that for each [`CustomType`]  the corresponding [`TypeDef`]
        ///  is in the [`ExtensionRegistry`] and the type arguments validate (recursively)
        /// and fit into the declared parameters of the [`TypeDef`].
        ///
        /// [`TypeDef`]: crate::extension::TypeDef
        fn validate(&self, var_decls: &[TypeParam]) -> Result<(), SignatureError>;

        /// Applies a [`Substitution`] to this instance, returning a new value.
        ///
        /// Infallible (assuming the `subst` covers all variables) and will
        /// not invalidate the instance (assuming all values substituted in are
        /// valid instances of the variables they replace).
        ///
        /// # Panics
        ///
        /// If the substitution does not cover all type variables in `self`.
        fn substitute(&self, s: &Substitution) -> Self;
    }
}

pub(crate) use internal::TypeRowLike;

impl TypeRowLike for TypeRow {
    fn validate(&self, var_decls: &[TypeParam]) -> Result<(), SignatureError> {
        self.iter().try_for_each(|t| t.validate(var_decls))
    }

    fn substitute(&self, s: &Substitution) -> Self {
        self.iter()
            .map(|ty| ty.substitute(s))
            .collect::<Vec<_>>()
            .into()
    }
}

impl Transformable for TypeRow {
    fn transform<T: TypeTransformer>(&mut self, tr: &T) -> Result<bool, T::Err> {
        self.to_mut().transform(tr)
    }
}

impl TypeRow {
    delegate! {
        to self.types {
            /// Returns the number of types in the row.
            #[must_use] pub fn len(&self) -> usize;

            #[inline(always)]
            /// Returns the type at the specified index. Returns `None` if out of bounds.
            #[must_use] pub fn get(&self, offset: usize) -> Option<&Type>;
        }

        to self.types.to_mut() {
            #[inline(always)]
            /// Returns the type at the specified index. Returns `None` if out of bounds.
            pub fn get_mut(&mut self, offset: usize) -> Option<&mut Type>;
        }
    }
}

impl Default for TypeRow {
    fn default() -> Self {
        Self::new()
    }
}

impl From<Vec<Type>> for TypeRow {
    fn from(types: Vec<Type>) -> Self {
        Self {
            types: types.into(),
        }
    }
}

impl TryFrom<Vec<Term>> for TypeRow {
    type Error = TermTypeError;

    fn try_from(value: Vec<Term>) -> Result<Self, Self::Error> {
        value
            .into_iter()
            .map(Type::try_from)
            .collect::<Result<Vec<_>, _>>()
            .map(Self::from)
    }
}

impl TryFrom<TypeRowRV> for TypeRow {
    type Error = TermTypeError;

    fn try_from(value: TypeRowRV) -> Result<Self, Self::Error> {
        value.0.try_into()
    }
}

impl<const N: usize> From<[Type; N]> for TypeRow {
    fn from(types: [Type; N]) -> Self {
        Self::from(Vec::from(types))
    }
}

impl From<&'static [Type]> for TypeRow {
    fn from(types: &'static [Type]) -> Self {
        Self {
            types: types.into(),
        }
    }
}

impl PartialEq<Term> for TypeRow {
    fn eq(&self, other: &Term) -> bool {
        let Term::List(items) = other else {
            return false;
        };
        if self.types.len() != items.len() {
            return false;
        }
        self.types.iter().zip_eq(items).all(|(ty, tm)| &**ty == tm)
    }
}

impl PartialEq<TypeRowRV> for TypeRow {
    fn eq(&self, other: &TypeRowRV) -> bool {
        self == &other.0
    }
}

/// Fallibly convert a [Term] to a [TypeRow].
///
/// This will fail if `arg` is not a [Term::List] or any of the elements are not [Type]s
impl TryFrom<Term> for TypeRow {
    type Error = TermTypeError;

    fn try_from(value: Term) -> Result<Self, Self::Error> {
        match value {
            Term::List(elems) => Ok(elems
                .into_iter()
                .map(Type::try_from)
                .collect::<Result<Vec<_>, _>>()?
                .into()),
            v => Err(TermTypeError::InvalidValue(Box::new(v))),
        }
    }
}

impl From<TypeRow> for Term {
    fn from(value: TypeRow) -> Self {
        Term::new_list(value.into_owned().into_iter().map_into())
    }
}

impl From<TypeRow> for TypeRowRV {
    fn from(value: TypeRow) -> Self {
        Self(Term::from(value))
    }
}

impl Deref for TypeRow {
    type Target = [Type];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl DerefMut for TypeRow {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.types.to_mut()
    }
}

/// Row of types and/or row variables, the number of actual types is thus
/// unknown. Used for opdef signatures, and types of runtime function pointers.
///
/// A [Term] that `check_term_type`s against [Term::ListKind] of [Term::TypeKind]
/// (of a [TypeBound]), i.e. one of
/// * A [Term::Variable] of type [Term::ListKind] (of [Term::TypeKind]...)
/// * A [Term::List], each of whose elements is of type some [Term::TypeKind]
/// * A [Term::ListConcat], each of whose sublists is one of these three
///
/// [TypeBound]: crate::types::TypeBound
#[derive(Clone, Debug, Display, PartialEq, Eq, Hash)]
#[display("{_0}")]
pub struct TypeRowRV(pub(super) Term);

impl TypeRowRV {
    const EMPTY: TypeRowRV = Self(Term::List(vec![]));
    pub(super) const EMPTY_REF: &TypeRowRV = &Self::EMPTY;

    /// Create a new empty row.
    pub const fn new() -> Self {
        Self::EMPTY
    }

    /// Wraps the given Term, without checking its type.
    pub fn new_unchecked(t: impl Into<Term>) -> Self {
        Self(t.into())
    }

    /// Creates a singleton row with just a row variable
    /// (a variable ranging over lists of types of any length)
    pub fn just_row_var(idx: usize, b: TypeBound) -> Self {
        Self(Term::new_row_var_use(idx, b))
    }

    /// Concatenates another TypeRowRV onto the end of this one
    pub fn concat(self, other: impl Into<Self>) -> Self {
        Self(Term::concat_lists([self.0, other.into().0]))
    }

    /// Returns `true` if the row contains no types.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty_list()
    }
}

impl TypeRowLike for TypeRowRV {
    /// Checks that this is indeed a list of runtime types;
    /// and that all variables are as declared in the supplied list of params.
    fn validate(&self, vars: &[TypeParam]) -> Result<(), SignatureError> {
        check_term_type(&self.0, &Term::new_list_type(TypeBound::Linear))?;
        self.0.validate(vars)
    }

    fn substitute(&self, s: &Substitution) -> Self {
        // Substitution cannot make this invalid if it was valid previously
        Self::new_unchecked(self.0.substitute(s))
    }
}

impl Default for TypeRowRV {
    /// Makes a new empty list
    fn default() -> Self {
        Self::EMPTY
    }
}

impl Transformable for TypeRowRV {
    fn transform<T: TypeTransformer>(&mut self, t: &T) -> Result<bool, T::Err> {
        self.0.transform(t)
    }
}

impl std::ops::Deref for TypeRowRV {
    type Target = Term;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl TryFrom<Term> for TypeRowRV {
    type Error = TermTypeError;

    fn try_from(t: Term) -> Result<Self, Self::Error> {
        check_term_type(&t, &Term::new_list_type(TypeBound::Linear))?;
        Ok(Self(t))
    }
}

impl From<TypeRowRV> for Term {
    fn from(value: TypeRowRV) -> Self {
        value.0
    }
}

// This allows an easy syntax for building TypeRowRV's which are all Types
impl<T: IntoIterator<Item = Type>> From<T> for TypeRowRV {
    fn from(value: T) -> Self {
        Self(Term::new_list(value.into_iter().map_into()))
    }
}

/*impl FromIterator<Type> for TypeRowRV {
    fn from_iter<T: IntoIterator<Item = Type>>(iter: T) -> Self {
        Self(Term::new_list(iter.into_iter().map_into()))
    }
}*/

#[cfg(test)]
mod test {
    use super::*;
    use crate::{extension::prelude::bool_t, types::Type};

    mod proptest {
        use crate::proptest::RecursionDepth;
        use crate::types::{Term, Type, TypeBound, TypeRow, TypeRowRV};
        use ::proptest::prelude::*;

        impl Arbitrary for TypeRow {
            type Parameters = RecursionDepth;
            type Strategy = BoxedStrategy<Self>;
            fn arbitrary_with(depth: Self::Parameters) -> Self::Strategy {
                use proptest::collection::vec;
                if depth.leaf() {
                    Just(TypeRow::new()).boxed()
                } else {
                    vec(any_with::<Type>(depth.descend()), 0..4)
                        .prop_map(|ts| ts.clone().into())
                        .boxed()
                }
            }
        }

        impl Arbitrary for TypeRowRV {
            type Parameters = RecursionDepth;
            type Strategy = BoxedStrategy<Self>;
            fn arbitrary_with(depth: Self::Parameters) -> Self::Strategy {
                use proptest::collection::vec;
                if depth.leaf() {
                    Just(TypeRowRV::default()).boxed()
                } else {
                    prop_oneof![
                        vec(any_with::<Type>(depth.descend()), 0..4)
                            .prop_map(|ts| ts.clone().into())
                            .boxed(),
                        (any::<usize>(), any::<TypeBound>())
                            .prop_map(|(idx, b)| TypeRowRV::just_row_var(idx, b))
                            .boxed(),
                    ]
                    .boxed()
                }
            }
        }

        proptest! {
            #[test]
            fn type_row_rv_term_roundtrip(tr: TypeRowRV) {
                let t: Term = tr.clone().into();
                let tr2: TypeRowRV = t.try_into().unwrap();
                assert_eq!(tr, tr2);
            }
        }
    }

    #[test]
    fn test_try_from_term_to_typerow() {
        // Test successful conversion with List
        let types = vec![Type::new_unit_sum(1), bool_t()];
        let term = Term::new_list(types.iter().cloned().map_into());
        assert_eq!(
            TypeRow::try_from(term.clone()),
            Ok(TypeRow::from(types.clone()))
        );
        assert_eq!(
            TypeRowRV::try_from(term.clone()),
            Ok(TypeRowRV::from(types.clone()))
        );
        assert_eq!(*TypeRowRV::try_from(term.clone()).unwrap(), term);

        // Test failure with non-list
        let term = Term::from(Type::UNIT);
        assert!(TypeRow::try_from(term.clone()).is_err());
        assert!(TypeRowRV::try_from(term).is_err());

        assert!(TypeRow::try_from(Term::new_row_var_use(0, TypeBound::Linear)).is_err());
    }

    #[test]
    fn test_from_typerow_to_term() {
        let types = vec![Type::UNIT, bool_t()];
        let type_row = TypeRow::from(types);
        let term = Term::from(type_row.clone());

        match &term {
            Term::List(elems) => {
                assert_eq!(elems.len(), 2);
            }
            _ => panic!("Expected Term::List"),
        }

        assert_eq!(term.try_into(), Ok(type_row));
    }
}
