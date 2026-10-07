#![allow(missing_docs)]

use std::str::FromStr;

use hugr_model::v0 as model;
use hugr_model::v0::ast;
use model::bumpalo::Bump;
use pretty_assertions::assert_eq;

/// Reads a module from a string, serializes it to binary, and then deserializes it back to a module.
/// The original and deserialized modules are compared for equality.
pub fn binary_roundtrip(input: &str) {
    let bump = Bump::new();
    let package = ast::Package::from_str(input).unwrap();
    let package = package.resolve(&bump).unwrap();
    let bytes = model::binary::write_to_vec(&package);
    let deserialized_package = model::binary::read_from_slice(&bytes, &bump).unwrap();
    assert_eq!(package, deserialized_package);
}

#[test]
pub fn test_add() {
    binary_roundtrip(include_str!("fixtures/model-add.edn"));
}

#[test]
pub fn test_alias() {
    binary_roundtrip(include_str!("fixtures/model-alias.edn"));
}

#[test]
pub fn test_call() {
    binary_roundtrip(include_str!("fixtures/model-call.edn"));
}

#[test]
pub fn test_cfg() {
    binary_roundtrip(include_str!("fixtures/model-cfg.edn"));
}

#[test]
pub fn test_cond() {
    binary_roundtrip(include_str!("fixtures/model-cond.edn"));
}

#[test]
pub fn test_loop() {
    binary_roundtrip(include_str!("fixtures/model-loop.edn"));
}

#[test]
pub fn test_params() {
    binary_roundtrip(include_str!("fixtures/model-params.edn"));
}

#[test]
pub fn test_decl_exts() {
    binary_roundtrip(include_str!("fixtures/model-decl-exts.edn"));
}

#[test]
pub fn test_constraints() {
    binary_roundtrip(include_str!("fixtures/model-constraints.edn"));
}

#[test]
pub fn test_lists() {
    binary_roundtrip(include_str!("fixtures/model-lists.edn"));
}

#[test]
pub fn test_const() {
    binary_roundtrip(include_str!("fixtures/model-const.edn"));
}

#[test]
pub fn test_entrypoint() {
    binary_roundtrip(include_str!("fixtures/model-entrypoint.edn"));
}

#[test]
pub fn test_versioned_symbols() {
    binary_roundtrip(include_str!("fixtures/model-versioned-symbols.edn"));
}

#[test]
fn signed_zero_literals_preserve_their_sign() {
    // Signed zeroes affect `atan2`: for example, `atan2(+0.0, -0.0)` is +π,
    // whereas `atan2(+0.0, +0.0)` is +0.0. They must not be merged on round-trip.
    for values in [[0.0_f64, -0.0_f64], [-0.0_f64, 0.0_f64]] {
        let source = format!(
            "(hugr 0) (mod) (meta {:?}) (meta {:?})",
            values[0], values[1]
        );
        let package: ast::Package = source.parse().unwrap();
        let bump = Bump::new();
        let resolved = package.resolve(&bump).unwrap();
        let bytes = model::binary::write_to_vec(&resolved);
        let decoded = model::binary::read_from_slice(&bytes, &bump).unwrap();
        let restored = decoded.as_ast().unwrap();

        let actual: Vec<_> = restored.modules[0]
            .root
            .meta
            .iter()
            .map(|term| {
                let ast::Term::Literal(model::Literal::Float(value)) = term else {
                    panic!("expected float literal");
                };
                value.0.to_bits()
            })
            .collect();

        assert_eq!(actual, values.map(f64::to_bits));
    }
}
