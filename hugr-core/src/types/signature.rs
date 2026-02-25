//! Abstract and concrete Signature types.

use itertools::{Either, Itertools as _};

use std::fmt::{self, Display};

use super::type_param::TypeParam;
use super::{Substitution, Transformable, Type, TypeRow, TypeTransformer};

use crate::core::PortIndex;
use crate::extension::resolution::{
    ExtensionCollectionError, WeakExtensionRegistry, collect_signature_exts,
};
use crate::extension::{ExtensionRegistry, ExtensionSet, SignatureError};
use crate::types::{Term, TypeRowRV};
use crate::{Direction, IncomingPort, OutgoingPort, Port};

/// The concept of "signature" in the spec - a list of inputs and outputs being
/// the edges required to/from a node or within a [`FuncDefn`].
///
/// [`FuncDefn`]: crate::ops::FuncDefn
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Signature {
    /// Value inputs of the function.
    ///
    /// Each *element* must [check_term_type] against [Term::RuntimeType] of
    /// [TypeBound::Linear], hence the arity is fixed as the length of the row.
    pub input: TypeRow,
    /// Value outputs of the function.
    ///
    /// /// Each *element* must [check_term_type] against [Term::RuntimeType] of
    /// [TypeBound::Linear], hence the arity is fixed as the length of the row.
    pub output: TypeRow,
}

/// A function value whose number of inputs and outputs may be unknown.
///
/// ([FuncValueType::input] and [FuncValueType::output] are arbitrary [Term]s.)
///
/// Each must type-check against [Term::ListType]`(`Term::RuntimeType`(`[TypeBound::Linear]`))`
/// so can include variables containing unknown numbers of types.
///
/// Used for [`OpDef`]'s and may be used as a type (of function-pointer values)
/// on wires of a Hugr (see [`Type::new_function`]) but not a valid node type.
///
/// [`OpDef`]: crate::extension::OpDef
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct FuncValueType {
    /// Value inputs of the function.
    pub input: TypeRowRV,
    /// Value outputs of the function.
    pub output: TypeRowRV,
}

macro_rules! func_type_general {
    ($ft: ty, $io: ty) => {
        impl Transformable for $ft {
            fn transform<T: TypeTransformer>(&mut self, tr: &T) -> Result<bool, T::Err> {
                // TODO handle extension sets?
                Ok(self.input.transform(tr)? | self.output.transform(tr)?)
            }
        }

        impl Display for $ft {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                self.input.fmt(f)?;
                f.write_str(" -> ")?;
                self.output.fmt(f)
            }
        }

        impl $ft {
            #[inline]
            /// Returns a row of the value inputs of the function.
            #[must_use]
            pub fn input(&self) -> &$io {
                &self.input
            }

            #[inline]
            /// Returns a row of the value outputs of the function.
            #[must_use]
            pub fn output(&self) -> &$io {
                &self.output
            }

            #[inline]
            /// Returns a tuple with the input and output rows of the function.
            #[must_use]
            pub fn io(&self) -> (&$io, &$io) {
                (&self.input, &self.output)
            }

            pub(crate) fn substitute(&self, tr: &Substitution) -> Self {
                Self {
                    input: self.input.substitute(tr),
                    output: self.output.substitute(tr),
                }
            }
        }
    };
}

func_type_general!(Signature, TypeRow);
func_type_general!(FuncValueType, Term);

impl FuncValueType {
    /// Create a new FuncValueType with specified inputs and outputs.
    pub fn new(input: impl Into<TypeRowRV>, output: impl Into<TypeRowRV>) -> Self {
        let input = input.into();
        let output = output.into();
        Self { input, output }
    }

    /// Create a new signature with the same input and output types (signature of an endomorphic
    /// function).
    pub fn new_endo(row: impl Into<TypeRowRV>) -> Self {
        let row = row.into();
        Self::new(row.clone(), row)
    }

    // ALAN definitely opportunities to deduplicate between Signature/FuncValueType here...
    pub(super) fn validate(&self, var_decls: &[TypeParam]) -> Result<(), SignatureError> {
        self.input.validate(var_decls)?;
        self.output.validate(var_decls)
    }

    /// True if both inputs and outputs are necessarily empty
    /// (even after any possible substitution of row variables)
    #[inline(always)]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.input.is_empty_list() && self.output.is_empty_list()
    }
}

impl Signature {
    /// Create a new signature with specified inputs and outputs.
    pub fn new(input: impl Into<TypeRow>, output: impl Into<TypeRow>) -> Self {
        Self {
            input: input.into(),
            output: output.into(),
        }
    }

    /// Create a new signature with the same input and output types (signature of an endomorphic
    /// function).
    pub fn new_endo(row: impl Into<TypeRow>) -> Self {
        let row = row.into();
        Self::new(row.clone(), row)
    }

    pub(super) fn validate(&self, var_decls: &[TypeParam]) -> Result<(), SignatureError> {
        self.input.validate(var_decls)?;
        self.output.validate(var_decls)?;
        Ok(())
    }

    /// True if both inputs and outputs are empty.
    #[inline(always)]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.input.is_empty() && self.output.is_empty()
    }

    /// Returns a registry with the concrete extensions used by this signature.
    pub fn used_extensions(&self) -> Result<ExtensionRegistry, ExtensionCollectionError> {
        let mut used = WeakExtensionRegistry::default();
        let mut missing = ExtensionSet::new();

        collect_signature_exts(self, &mut used, &mut missing);

        if missing.is_empty() {
            Ok(used.try_into().expect("all extensions are present"))
        } else {
            Err(ExtensionCollectionError::dropped_signature(self, missing))
        }
    }

    /// Returns the type of a value [`Port`]. Returns `None` if the port is out
    /// of bounds.
    #[inline]
    pub fn port_type(&self, port: impl Into<Port>) -> Option<&Type> {
        let port: Port = port.into();
        match port.as_directed() {
            Either::Left(port) => self.in_port_type(port),
            Either::Right(port) => self.out_port_type(port),
        }
    }

    /// Returns the type of a value input [`Port`]. Returns `None` if the port is out
    /// of bounds.
    #[inline]
    pub fn in_port_type(&self, port: impl Into<IncomingPort>) -> Option<&Type> {
        self.input.get(port.into().index())
    }

    /// Returns the type of a value output [`Port`]. Returns `None` if the port is out
    /// of bounds.
    #[inline]
    pub fn out_port_type(&self, port: impl Into<OutgoingPort>) -> Option<&Type> {
        self.output.get(port.into().index())
    }

    /// Returns a mutable reference to the type of a value input [`Port`]. Returns `None` if the port is out
    /// of bounds.
    #[inline]
    pub fn in_port_type_mut(&mut self, port: impl Into<IncomingPort>) -> Option<&mut Type> {
        self.input.get_mut(port.into().index())
    }

    /// Returns the type of a value output [`Port`]. Returns `None` if the port is out
    /// of bounds.
    #[inline]
    pub fn out_port_type_mut(&mut self, port: impl Into<OutgoingPort>) -> Option<&mut Type> {
        self.output.get_mut(port.into().index())
    }

    /// Returns a mutable reference to the type of a value [`Port`].
    /// Returns `None` if the port is out of bounds.
    #[inline]
    pub fn port_type_mut(&mut self, port: impl Into<Port>) -> Option<&mut Type> {
        let port = port.into();
        match port.as_directed() {
            Either::Left(port) => self.in_port_type_mut(port),
            Either::Right(port) => self.out_port_type_mut(port),
        }
    }

    /// Returns the number of ports in the signature.
    #[inline]
    #[must_use]
    pub fn port_count(&self, dir: Direction) -> usize {
        match dir {
            Direction::Incoming => self.input.len(),
            Direction::Outgoing => self.output.len(),
        }
    }

    /// Returns the number of input ports in the signature.
    #[inline]
    #[must_use]
    pub fn input_count(&self) -> usize {
        self.port_count(Direction::Incoming)
    }

    /// Returns the number of output ports in the signature.
    #[inline]
    #[must_use]
    pub fn output_count(&self) -> usize {
        self.port_count(Direction::Outgoing)
    }

    /// Returns a slice of the types for the given direction.
    #[inline]
    #[must_use]
    pub fn types(&self, dir: Direction) -> &[Type] {
        match dir {
            Direction::Incoming => &self.input,
            Direction::Outgoing => &self.output,
        }
    }

    /// Returns a slice of the input types.
    #[inline]
    #[must_use]
    pub fn input_types(&self) -> &[Type] {
        self.types(Direction::Incoming)
    }

    /// Returns a slice of the output types.
    #[inline]
    #[must_use]
    pub fn output_types(&self) -> &[Type] {
        self.types(Direction::Outgoing)
    }

    /// Returns the `Port`s in the signature for a given direction.
    #[inline]
    pub fn ports(&self, dir: Direction) -> impl Iterator<Item = Port> + use<> {
        (0..self.port_count(dir)).map(move |i| Port::new(dir, i))
    }

    /// Returns the incoming `Port`s in the signature.
    #[inline]
    pub fn input_ports(&self) -> impl Iterator<Item = IncomingPort> + use<> {
        self.ports(Direction::Incoming)
            .map(|p| p.as_incoming().unwrap())
    }

    /// Returns the outgoing `Port`s in the signature.
    #[inline]
    pub fn output_ports(&self) -> impl Iterator<Item = OutgoingPort> + use<> {
        self.ports(Direction::Outgoing)
            .map(|p| p.as_outgoing().unwrap())
    }
}

impl TryFrom<FuncValueType> for Signature {
    type Error = SignatureError;

    fn try_from(value: FuncValueType) -> Result<Self, Self::Error> {
        let input: TypeRow = value.input.try_into()?;
        let output: TypeRow = value.output.try_into()?;
        Ok(Self::new(input, output))
    }
}

impl From<Signature> for FuncValueType {
    fn from(value: Signature) -> Self {
        Self {
            input: value.input.into(),
            output: value.output.into(),
        }
    }
}

impl PartialEq<Signature> for FuncValueType {
    fn eq(&self, other: &Signature) -> bool {
        let (Term::List(ins), Term::List(outs)) = (&self.input.0, &self.output.0) else {
            return false;
        };
        fn eq(xs: &[Type], ys: &[Term]) -> bool {
            xs.len() == ys.len() && xs.iter().zip_eq(ys).all(|(x, y)| &**x == y)
        }
        eq(&other.input, ins) && eq(&other.output, outs)
    }
}

#[cfg(test)]
mod test {
    use proptest::prelude::{Arbitrary, BoxedStrategy, Strategy, any, any_with};
    use proptest::{collection::vec, strategy::Union};

    use crate::extension::prelude::{bool_t, qb_t, usize_t};
    use crate::proptest::RecursionDepth;
    use crate::type_row;
    use crate::types::TypeBound;
    use crate::types::test::FnTransformer;
    use crate::types::{CustomType, TypeRow, type_param::SeqPart};

    use super::*;

    impl Arbitrary for Signature {
        type Parameters = RecursionDepth;
        fn arbitrary_with(depth: Self::Parameters) -> Self::Strategy {
            let input_strategy = any_with::<TypeRow>(depth);
            let output_strategy = any_with::<TypeRow>(depth);
            (input_strategy, output_strategy)
                .prop_map(|(input, output)| Signature::new(input, output))
                .boxed()
        }
        type Strategy = BoxedStrategy<Self>;
    }

    impl Arbitrary for FuncValueType {
        type Parameters = RecursionDepth;
        fn arbitrary_with(depth: Self::Parameters) -> Self::Strategy {
            let io_strategy = vec(
                Union::new([
                    any_with::<Type>(depth)
                        .prop_map(Term::from)
                        .prop_map(SeqPart::Item)
                        .boxed(),
                    (any::<usize>(), any::<TypeBound>())
                        .prop_map(|(idx, bound)| SeqPart::Splice(Term::new_row_var_use(idx, bound)))
                        .boxed(),
                ]),
                0..3,
            )
            .prop_map(|parts| TypeRowRV::try_from(Term::new_list_from_parts(parts)).unwrap());
            (io_strategy.clone(), io_strategy)
                .prop_map(|(input, output)| FuncValueType::new(input, output))
                .boxed()
        }
        type Strategy = BoxedStrategy<Self>;
    }

    #[test]
    fn test_function_type() {
        let mut f_type = Signature::new(type_row![Type::UNIT], type_row![Type::UNIT]);
        assert_eq!(f_type.input_count(), 1);
        assert_eq!(f_type.output_count(), 1);

        assert_eq!(f_type.input_types(), &[Type::UNIT]);

        assert_eq!(
            f_type.port_type(Port::new(Direction::Incoming, 0)),
            Some(&Type::UNIT)
        );

        let out = Port::new(Direction::Outgoing, 0);
        *(f_type.port_type_mut(out).unwrap()) = usize_t();

        assert_eq!(f_type.port_type(out), Some(&usize_t()));

        assert_eq!(f_type.input_types(), &[Type::UNIT]);
        assert_eq!(f_type.output_types(), &[usize_t()]);
        assert_eq!(
            f_type.io(),
            (&type_row![Type::UNIT], &vec![usize_t()].into())
        );
    }

    #[test]
    fn test_transform() {
        let Term::RuntimeExtension(usz_t) = usize_t().into() else {
            panic!()
        };
        let tr = FnTransformer(|ct: &CustomType| (ct == &usz_t).then_some(bool_t()));
        let row_with = || TypeRow::from(vec![usize_t(), qb_t(), bool_t()]);
        let row_after = || TypeRow::from(vec![bool_t(), qb_t(), bool_t()]);
        let mut sig = Signature::new(row_with(), row_after());
        let exp = Signature::new(row_after(), row_after());
        assert_eq!(sig.transform(&tr), Ok(true));
        assert_eq!(sig, exp);
        assert_eq!(sig.transform(&tr), Ok(false));
        assert_eq!(sig, exp);
        let exp = Type::new_function(exp);
        for fty in [
            FuncValueType::new(row_after(), row_with()),
            FuncValueType::new(row_with(), row_with()),
        ] {
            let mut t = Type::new_function(fty);
            assert_eq!(t.transform(&tr), Ok(true));
            assert_eq!(t, exp);
            assert_eq!(t.transform(&tr), Ok(false));
            assert_eq!(t, exp);
        }
    }
}
