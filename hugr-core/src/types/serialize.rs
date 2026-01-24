use std::sync::Arc;

use ordered_float::OrderedFloat;
use serde::Serialize;
use serde_with::serde_as;

use super::{FuncValueType, SumType, TypeBound};

use super::custom::CustomType;

use crate::extension::SignatureError;
use crate::extension::prelude::{qb_t, usize_t};
use crate::ops::AliasDecl;
use crate::types::type_param::{SeqPart, TermTypeError, TermVar, UpperBound};
use crate::types::{GeneralSum, Term, Type, sum_bound};

#[derive(serde::Serialize, serde::Deserialize, Clone, Debug)]
#[serde(tag = "t")]
pub(crate) enum SerSimpleType {
    Q,
    I,
    G(Box<FuncValueType>),
    Sum(SumType),
    Opaque(CustomType),
    Alias(AliasDecl),
    V { i: usize, b: TypeBound },
    R { i: usize, b: TypeBound },
}

/// For the things that used to be supported as Types
impl TryFrom<Type> for SerSimpleType {
    type Error = SignatureError;
    fn try_from(value: Type) -> Result<Self, SignatureError> {
        if value == qb_t() {
            return Ok(SerSimpleType::Q);
        }
        if value == usize_t() {
            return Ok(SerSimpleType::I);
        }
        match value {
            Term::RuntimeExtension(o) => Ok(SerSimpleType::Opaque(o)),
            //TypeEnum::Alias(a) => SerSimpleType::Alias(a),
            Term::RuntimeFunction(sig) => Ok(SerSimpleType::G(sig)),
            Term::Variable(tv) => {
                let i = tv.index();
                match &*tv.cached_decl {
                    Term::RuntimeType(b) => return Ok(SerSimpleType::V { i, b: *b }),
                    Term::ListType(b) => match &**b {
                        Term::RuntimeType(b) => return Ok(SerSimpleType::R { i, b: *b }),
                        _ => (),
                    },
                    _ => (),
                };
                Err(SignatureError::TypeArgMismatch(
                    TermTypeError::InvalidValue(tv.cached_decl),
                ))
            }
            Term::RuntimeSum(st) => Ok(SerSimpleType::Sum(st)),
            _ => {
                todo!("Only Custom types, functions, sums and variables supported ATM");
                return Err(SignatureError::InvalidTypeArgs);
            }
        }
    }
}

impl From<SerSimpleType> for Term {
    fn from(value: SerSimpleType) -> Self {
        match value {
            SerSimpleType::Q => qb_t(),
            SerSimpleType::I => usize_t(),
            SerSimpleType::G(sig) => Type::new_function(*sig),
            SerSimpleType::Sum(st) => st.into(),
            SerSimpleType::Opaque(o) => Type::new_extension(o),
            SerSimpleType::Alias(_) => todo!("alias?"),
            SerSimpleType::V { i, b } => Type::new_var_use(i, b),
            SerSimpleType::R { i, b } => Type::new_row_var_use(i, b),
        }
    }
}

#[derive(Clone, Debug, serde::Deserialize, serde::Serialize)]
#[non_exhaustive]
#[serde(tag = "tp")]
pub(super) enum TypeParamSer {
    Type { b: TypeBound },
    BoundedNat { bound: UpperBound },
    String,
    Bytes,
    Float,
    StaticType,
    List { param: Box<Term> },
    Tuple { params: ArrayOrTermSer },
    ConstType { ty: Type },
}

#[derive(Clone, Debug, serde::Deserialize, serde::Serialize)]
#[non_exhaustive]
#[serde(tag = "tya")]
pub(super) enum TypeArgSer {
    Type {
        ty: SerSimpleType,
    },
    BoundedNat {
        n: u64,
    },
    String {
        arg: String,
    },
    Bytes {
        #[serde(with = "base64")]
        value: Arc<[u8]>,
    },
    Float {
        value: OrderedFloat<f64>,
    },
    List {
        elems: Vec<Term>,
    },
    ListConcat {
        lists: Vec<Term>,
    },
    Tuple {
        elems: Vec<Term>,
    },
    TupleConcat {
        tuples: Vec<Term>,
    },
    Variable {
        #[serde(flatten)]
        v: TermVar,
    },
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
pub(super) enum TermSer {
    TypeArg(TypeArgSer),
    TypeParam(TypeParamSer),
}

impl From<Term> for TermSer {
    fn from(value: Term) -> Self {
        match value {
            Term::RuntimeType(b) => TermSer::TypeParam(TypeParamSer::Type { b }),
            Term::StaticType => TermSer::TypeParam(TypeParamSer::StaticType),
            Term::BoundedNatType(bound) => TermSer::TypeParam(TypeParamSer::BoundedNat { bound }),
            Term::StringType => TermSer::TypeParam(TypeParamSer::String),
            Term::BytesType => TermSer::TypeParam(TypeParamSer::Bytes),
            Term::FloatType => TermSer::TypeParam(TypeParamSer::Float),
            Term::ListType(param) => TermSer::TypeParam(TypeParamSer::List { param }),
            Term::ConstType(ty) => TermSer::TypeParam(TypeParamSer::ConstType { ty: *ty }),
            Term::RuntimeFunction(_) | Term::RuntimeExtension(_) | Term::RuntimeSum(_) => {
                TermSer::TypeArg(TypeArgSer::Type {
                    ty: value.try_into().unwrap(),
                })
            }
            Term::TupleType(params) => TermSer::TypeParam(TypeParamSer::Tuple {
                params: (*params).into(),
            }),
            Term::BoundedNat(n) => TermSer::TypeArg(TypeArgSer::BoundedNat { n }),
            Term::String(arg) => TermSer::TypeArg(TypeArgSer::String { arg }),
            Term::Bytes(value) => TermSer::TypeArg(TypeArgSer::Bytes { value }),
            Term::Float(value) => TermSer::TypeArg(TypeArgSer::Float { value }),
            Term::List(elems) => TermSer::TypeArg(TypeArgSer::List { elems }),
            Term::Tuple(elems) => TermSer::TypeArg(TypeArgSer::Tuple { elems }),
            Term::Variable(v) => TermSer::TypeArg(TypeArgSer::Variable { v }),
            Term::ListConcat(lists) => TermSer::TypeArg(TypeArgSer::ListConcat { lists }),
            Term::TupleConcat(tuples) => TermSer::TypeArg(TypeArgSer::TupleConcat { tuples }),
        }
    }
}

impl From<TermSer> for Term {
    fn from(value: TermSer) -> Self {
        match value {
            TermSer::TypeParam(param) => match param {
                TypeParamSer::Type { b } => Term::RuntimeType(b),
                TypeParamSer::StaticType => Term::StaticType,
                TypeParamSer::BoundedNat { bound } => Term::BoundedNatType(bound),
                TypeParamSer::String => Term::StringType,
                TypeParamSer::Bytes => Term::BytesType,
                TypeParamSer::Float => Term::FloatType,
                TypeParamSer::List { param } => Term::ListType(param),
                TypeParamSer::Tuple { params } => Term::TupleType(Box::new(params.into())),
                TypeParamSer::ConstType { ty } => Term::ConstType(Box::new(ty)),
            },
            TermSer::TypeArg(arg) => match arg {
                TypeArgSer::Type { ty } => Term::from(ty),
                TypeArgSer::BoundedNat { n } => Term::BoundedNat(n),
                TypeArgSer::String { arg } => Term::String(arg),
                TypeArgSer::Bytes { value } => Term::Bytes(value),
                TypeArgSer::Float { value } => Term::Float(value),
                TypeArgSer::List { elems } => Term::List(elems),
                TypeArgSer::Tuple { elems } => Term::Tuple(elems),
                TypeArgSer::Variable { v } => Term::Variable(v),
                TypeArgSer::ListConcat { lists } => Term::ListConcat(lists),
                TypeArgSer::TupleConcat { tuples } => Term::TupleConcat(tuples),
            },
        }
    }
}

/// Helper for use with [serde_with::serde_as] to serialize
/// a [TypeRow] *all of whose elements are types* in legacy Json
// ALAN TODO just do this by default for all TypeRows? (Unless overridden?)
pub(crate) enum SerTypeRow {}

/// Helper for use with [serde_with::serde_as] to serialize a [Term]
/// that is an instance of [`Term::ListType`]([`Term::RuntimeType`](...))
/// as a list of types + row variables
pub(crate) enum SerTypeRowRV {}

/// Helper to (de)serialize GeneralSums without storing the (cached) bound
#[serde_as]
#[derive(serde::Serialize, serde::Deserialize)]
pub(super) struct SerGenSum {
    #[serde_as(as = "Vec<crate::types::serialize::SerTypeRowRV>")]
    rows: Vec<Term>,
}

impl From<GeneralSum> for SerGenSum {
    fn from(value: GeneralSum) -> Self {
        Self {
            rows: value.rows.into_owned(),
        }
    }
}

impl From<SerGenSum> for GeneralSum {
    fn from(value: SerGenSum) -> Self {
        let bound = sum_bound(value.rows.iter());
        Self {
            rows: value.rows.into(),
            bound,
        }
    }
}

/// Helper type that serialises lists as JSON arrays for compatibility.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(untagged)]
pub(super) enum ArrayOrTermSer {
    Array(Vec<Term>),
    Term(Box<Term>), // TODO JSON Schema does not really support this yet
}

impl From<ArrayOrTermSer> for Term {
    fn from(value: ArrayOrTermSer) -> Self {
        match value {
            ArrayOrTermSer::Array(terms) => Term::new_list(terms),
            ArrayOrTermSer::Term(term) => *term,
        }
    }
}

impl From<Term> for ArrayOrTermSer {
    fn from(term: Term) -> Self {
        match term {
            Term::List(terms) => ArrayOrTermSer::Array(terms),
            term => ArrayOrTermSer::Term(Box::new(term)),
        }
    }
}

/// Helper for to serialize and deserialize the byte string in [`TypeArg::Bytes`] via base64.
mod base64 {
    use std::sync::Arc;

    use base64::Engine as _;
    use base64::prelude::BASE64_STANDARD;
    use serde::{Deserialize, Serialize};
    use serde::{Deserializer, Serializer};

    pub fn serialize<S: Serializer>(v: &Arc<[u8]>, s: S) -> Result<S::Ok, S::Error> {
        let base64 = BASE64_STANDARD.encode(v);
        base64.serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Arc<[u8]>, D::Error> {
        let base64 = String::deserialize(d)?;
        BASE64_STANDARD
            .decode(base64.as_bytes())
            .map(|v| v.into())
            .map_err(serde::de::Error::custom)
    }
}

pub(crate) mod sertype {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    use super::SerSimpleType;
    use crate::types::Term;

    pub fn serialize<S: Serializer>(ty: &Term, s: S) -> Result<S::Ok, S::Error> {
        SerSimpleType::try_from(ty.clone()).unwrap().serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deser: D) -> Result<Term, D::Error> {
        let sertype: SerSimpleType = Deserialize::deserialize(deser)?;
        Ok(sertype.into())
    }
}

impl serde_with::SerializeAs<Term> for SerTypeRowRV {
    fn serialize_as<S: serde::Serializer>(source: &Term, serializer: S) -> Result<S::Ok, S::Error> {
        let items: Vec<SerSimpleType> = source
            .clone()
            .into_list_parts()
            .map(|part| match part {
                SeqPart::Item(t) => {
                    let s = SerSimpleType::try_from(t).unwrap();
                    assert!(!matches!(s, SerSimpleType::R { .. }));
                    s
                }
                SeqPart::Splice(t) => {
                    let s = SerSimpleType::try_from(t).unwrap();
                    assert!(matches!(s, SerSimpleType::R { .. }));
                    s
                }
            })
            .collect();
        items.serialize(serializer)
    }
}

impl<'de> serde_with::DeserializeAs<'de, Term> for SerTypeRowRV {
    fn deserialize_as<D: serde::Deserializer<'de>>(deser: D) -> Result<Term, D::Error> {
        let items: Vec<SerSimpleType> = serde::Deserialize::deserialize(deser)?;
        let list_parts = items.into_iter().map(|s| match s {
            SerSimpleType::R { i, b } => SeqPart::Splice(Term::new_row_var_use(i, b)),
            s => SeqPart::Item(Term::from(s)),
        });
        Ok(Term::new_list_from_parts(list_parts))
    }
}
