//! Rows of types, used for function signatures,
//! designed to support efficient static allocation.

use std::{
    borrow::Cow,
    fmt::{self, Display, Write},
    ops::{Deref, DerefMut},
};

use super::{Substitution, Term, Transformable, Type, TypeTransformer, type_param::TypeParam};
use crate::{extension::SignatureError, types::type_param::TermTypeError, utils::display_list};
use delegate::delegate;
use itertools::Itertools;

/// List of types, used for function signatures.
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

/// Row of types and/or row variables, the number of actual types is thus
/// unknown
/// Legacy alias. Used to indicate a [Term] that `check_term_type`s against
/// [Term::ListType] of [Term::RuntimeType] (of a [TypeBound]), i.e. one of
/// * A [Term::Variable] of type [Term::ListType] (of [Term::RuntimeType]...)
/// * A [Term::List], each of whose elements is of type some [Term::RuntimeType]
/// * A [Term::ListConcat], each of whose sublists is one of these three
///
/// [TypeBound]: crate::types::TypeBound
pub type TypeRowRV = Term;

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

    /// Applies a substitution to the row.
    pub(crate) fn substitute(&self, s: &Substitution) -> Self {
        self.iter()
            .map(|ty| ty.substitute(s))
            .collect::<Vec<_>>()
            .into()
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

    pub(super) fn validate(&self, var_decls: &[TypeParam]) -> Result<(), SignatureError> {
        self.iter().try_for_each(|t| t.validate(var_decls))
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

/// Fallibly convert a [Term] to a [TypeRow].
///
/// This will fail if `arg` is not a [Term::List] or any of the elements are not [Type]s
impl TryFrom<Term> for TypeRow {
    type Error = SignatureError;

    fn try_from(value: Term) -> Result<Self, Self::Error> {
        match value {
            Term::List(elems) => Ok(elems
                .into_iter()
                .map(Type::try_from)
                .collect::<Result<Vec<_>, _>>()?
                .into()),
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }
}

impl From<TypeRow> for Term {
    fn from(value: TypeRow) -> Self {
        Term::new_list(value.into_owned().into_iter().map_into())
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::{extension::prelude::bool_t, types::Type};

    mod proptest {
        use super::super::TypeRow;
        use crate::{proptest::RecursionDepth, types::Type};
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
    }

    #[test]
    fn test_try_from_term_to_typerow() {
        // Test successful conversion with List
        let types = vec![Type::new_unit_sum(1), bool_t()];
        let term = Term::new_list(types.iter().cloned().map_into());
        let result = TypeRow::try_from(term);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), TypeRow::from(types));

        // Test failure with non-list
        let term = Term::from(Type::UNIT);
        let result = TypeRow::try_from(term);
        assert!(result.is_err());
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
