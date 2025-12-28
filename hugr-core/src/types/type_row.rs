//! Rows of types, used for function signatures,
//! designed to support efficient static allocation.

use std::{
    borrow::Cow,
    fmt::{self, Display, Write},
    ops::{Deref, DerefMut},
};

use super::{
    Substitution, Term, Transformable, Type, TypeArg, TypeTransformer, type_param::TypeParam,
};
use crate::{extension::SignatureError, utils::display_list};
use delegate::delegate;
use itertools::Itertools;

/// List of types/terms. Like a `Vec<`[Term]`>` but allows sharing via `Cow`
/// and static allocation via [type_row!].
#[derive(Clone, PartialEq, Eq, Debug, Hash, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
#[serde(transparent)]
pub struct TypeRow {
    /// The datatypes in the row.
    types: Cow<'static, [Term]>,
}

/// ALAN TODO Should remove this.
pub type TypeRowRV = TypeRow;

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

    pub fn new_from_list(value: Term) -> Result<Self, SignatureError> {
        match value {
            TypeArg::List(elems) => Ok(elems.into()),
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }

    /// Returns a new `TypeRow` with `xs` concatenated onto `self`.
    pub fn extend<'a>(&'a self, rest: impl IntoIterator<Item = &'a Term>) -> Self {
        self.iter().chain(rest).cloned().collect_vec().into()
    }

    /// Returns a reference to the types in the row.
    #[must_use]
    pub fn as_slice(&self) -> &[Term] {
        &self.types
    }

    /// Applies a substitution to the row.
    pub(crate) fn substitute(&self, s: &Substitution) -> Self {
        self.iter()
            .flat_map(|ty| ty.substitute(s))
            .collect::<Vec<_>>()
            .into()
    }

    delegate! {
        to self.types {
            /// Iterator over the types in the row.
            pub fn iter(&self) -> impl Iterator<Item = &Term>;

            /// Mutable vector of the types in the row.
            pub fn to_mut(&mut self) -> &mut Vec<Term>;

            /// Allow access (consumption) of the contained elements
            #[must_use] pub fn into_owned(self) -> Vec<Term>;

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

// ALAN these were considered only good to make available for non-RV TypeRows...
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

impl From<Vec<Term>> for TypeRow {
    fn from(types: Vec<Term>) -> Self {
        Self {
            types: types.into(),
        }
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

/// Fallibly convert a [Term] to a [TypeRowRV].
///
/// This will fail if `arg` is of non-sequence kind (e.g. Type).
impl TryFrom<Term> for TypeRow {
    type Error = SignatureError;

    fn try_from(value: Term) -> Result<Self, Self::Error> {
        match value {
            Term::List(elems) => Ok(Self::from(elems)),
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }
}

impl From<TypeRow> for Term {
    fn from(value: TypeRow) -> Self {
        Term::List(value.into_owned())
    }
}

impl Deref for TypeRow {
    type Target = [Term];

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
    use crate::{
        extension::prelude::bool_t,
        types::{Type, TypeArg, TypeRV},
    };

    mod proptest {
        use crate::proptest::RecursionDepth;
        use crate::types::{MaybeRV, TypeBase, TypeRowBase};
        use ::proptest::prelude::*;

        impl<RV: MaybeRV> Arbitrary for super::super::TypeRowBase<RV> {
            type Parameters = RecursionDepth;
            type Strategy = BoxedStrategy<Self>;
            fn arbitrary_with(depth: Self::Parameters) -> Self::Strategy {
                use proptest::collection::vec;
                if depth.leaf() {
                    Just(TypeRowBase::new()).boxed()
                } else {
                    vec(any_with::<TypeBase<RV>>(depth), 0..4)
                        .prop_map(|ts| ts.clone().into())
                        .boxed()
                }
            }
        }
    }

    #[test]
    fn test_try_from_term_to_typerv() {
        // Test successful conversion with Runtime type
        let runtime_type = Type::UNIT;
        let term = TypeArg::Runtime(runtime_type.clone());
        let result = TypeRV::try_from(term);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), TypeRV::from(runtime_type));

        // Test failure with non-type kind
        let term = Term::String("test".to_string());
        let result = TypeRV::try_from(term);
        assert!(result.is_err());
    }

    #[test]
    fn test_try_from_term_to_typerow() {
        // Test successful conversion with List
        let types = vec![Type::new_unit_sum(1), bool_t()];
        let type_args = types.iter().map(|t| TypeArg::Runtime(t.clone())).collect();
        let term = TypeArg::List(type_args);
        let result = TypeRow::try_from(term);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), TypeRow::from(types));

        // Test failure with non-list
        let term = TypeArg::Runtime(Type::UNIT);
        let result = TypeRow::try_from(term);
        assert!(result.is_err());
    }

    #[test]
    fn test_try_from_term_to_typerowrv() {
        // Test successful conversion with List
        let types = [TypeRV::from(Type::UNIT), TypeRV::from(bool_t())];
        let type_args = types.iter().map(|t| t.clone().into()).collect();
        let term = TypeArg::List(type_args);
        let result = TypeRowRV::try_from(term);
        assert!(result.is_ok());

        // Test failure with non-sequence kind
        let term = Term::String("test".to_string());
        let result = TypeRowRV::try_from(term);
        assert!(result.is_err());
    }

    #[test]
    fn test_from_typerow_to_term() {
        let types = vec![Type::UNIT, bool_t()];
        let type_row = TypeRow::from(types);
        let term = Term::from(type_row);

        match term {
            Term::List(elems) => {
                assert_eq!(elems.len(), 2);
            }
            _ => panic!("Expected Term::List"),
        }
    }

    #[test]
    fn test_from_typerowrv_to_term() {
        let types = vec![TypeRV::from(Type::UNIT), TypeRV::from(bool_t())];
        let type_row_rv = TypeRowRV::from(types);
        let term = Term::from(type_row_rv);

        match term {
            TypeArg::List(elems) => {
                assert_eq!(elems.len(), 2);
            }
            _ => panic!("Expected Term::List"),
        }
    }
}
