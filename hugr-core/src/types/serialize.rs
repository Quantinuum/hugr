use std::sync::Arc;

use ordered_float::OrderedFloat;
use serde::Serialize;

use super::{FuncValueType, SumType, Term, Type, TypeBound};

use super::custom::CustomType;

use crate::extension::prelude::{qb_t, usize_t};
use crate::ops::AliasDecl;
use crate::types::TypeRowRV;
use crate::types::type_param::{SeqPart, TermTypeError, TermVar, UpperBound};

#[derive(Serialize, serde::Deserialize, Clone, Debug)]
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
impl From<Type> for SerSimpleType {
    fn from(value: Type) -> Self {
        if value == qb_t() {
            return SerSimpleType::Q;
        }
        if value == usize_t() {
            return SerSimpleType::I;
        }
        match value.into() {
            Term::RuntimeExtension(o) => SerSimpleType::Opaque(o),
            //TypeEnum::Alias(a) => SerSimpleType::Alias(a),
            Term::RuntimeFunction(sig) => SerSimpleType::G(sig),
            Term::Variable(tv) => {
                let i = tv.index();
                let Term::RuntimeType(b) = &*tv.cached_decl else {
                    panic!("Variable with bound {} is not a valid Type", tv.cached_decl);
                };
                SerSimpleType::V { i, b: *b }
            }
            Term::RuntimeSum(st) => SerSimpleType::Sum(st),
            v => panic!("{} was not a valid Type", v),
        }
    }
}

impl TryFrom<Term> for SerSimpleType {
    type Error = TermTypeError;

    fn try_from(value: Term) -> Result<Self, Self::Error> {
        if let Term::Variable(tv) = &value
            && let Term::ListType(t) = &*tv.cached_decl
            && let Term::RuntimeType(b) = &**t
        {
            return Ok(SerSimpleType::R {
                i: tv.index(),
                b: *b,
            });
        }
        Type::try_from(value).map(SerSimpleType::from)
    }
}

impl From<SerSimpleType> for Term {
    fn from(value: SerSimpleType) -> Self {
        match value {
            SerSimpleType::Q => qb_t().into(),
            SerSimpleType::I => usize_t().into(),
            SerSimpleType::G(sig) => Type::new_function(*sig).into(),
            SerSimpleType::Sum(st) => Type::from(st).into(),
            SerSimpleType::Opaque(o) => Type::new_extension(o).into(),
            SerSimpleType::Alias(_) => todo!("alias?"),
            SerSimpleType::V { i, b } => Type::new_var_use(i, b).into(),
            SerSimpleType::R { i, b } => Term::new_row_var_use(i, b),
        }
    }
}

impl TryFrom<SerSimpleType> for Type {
    type Error = TermTypeError;

    fn try_from(value: SerSimpleType) -> Result<Self, Self::Error> {
        Term::from(value).try_into()
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

impl serde::Serialize for TypeRowRV {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let items: Vec<SerSimpleType> = self
            .0
            .clone()
            .into_list_parts()
            .map(|part| match part {
                SeqPart::Item(t) => {
                    let t = Type::try_from(t).unwrap();
                    let s = SerSimpleType::from(t);
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

impl<'de> serde::Deserialize<'de> for TypeRowRV {
    fn deserialize<D: serde::Deserializer<'de>>(deser: D) -> Result<Self, D::Error> {
        let items: Vec<SerSimpleType> = serde::Deserialize::deserialize(deser)?;
        let list_parts = items.into_iter().map(|s| match s {
            SerSimpleType::R { i, b } => SeqPart::Splice(Term::new_row_var_use(i, b)),
            s => SeqPart::Item(Term::from(s)),
        });
        Ok(TypeRowRV::try_from(Term::new_list_from_parts(list_parts)).unwrap())
    }
}
