#![allow(missing_docs)]

use hugr_model::v0::ast;
use rstest::rstest;
use std::str::FromStr as _;

fn roundtrip(source: &str) -> String {
    let package = ast::Package::from_str(source).unwrap();
    package.to_string()
}

#[rstest]
#[case::add(include_str!("fixtures/model-add.edn"))]
#[case::alias(include_str!("fixtures/model-alias.edn"))]
#[case::call(include_str!("fixtures/model-call.edn"))]
#[case::cfg(include_str!("fixtures/model-cfg.edn"))]
#[case::cond(include_str!("fixtures/model-cond.edn"))]
#[case::const_(include_str!("fixtures/model-const.edn"))]
#[case::constraints(include_str!("fixtures/model-constraints.edn"))]
#[case::decl_exts(include_str!("fixtures/model-decl-exts.edn"))]
#[case::entrypoint(include_str!("fixtures/model-entrypoint.edn"))]
#[case::lists(include_str!("fixtures/model-lists.edn"))]
#[case::literals(include_str!("fixtures/model-literals.edn"))]
#[case::loop_(include_str!("fixtures/model-loop.edn"))]
#[case::order(include_str!("fixtures/model-order.edn"))]
#[case::params(include_str!("fixtures/model-params.edn"))]
#[cfg_attr(miri, ignore)] // Opening files is not supported in (isolated) miri
pub fn test_roundtrip(#[case] expected: &str) {
    let actual = roundtrip(expected);
    // Trim whitespace from the strings to compare them
    let expected_trim = expected
        .split_whitespace()
        .fold(String::new(), |acc, s| acc + s);
    let actual_trim = actual
        .split_whitespace()
        .fold(String::new(), |acc, s| acc + s);
    assert_eq!(expected_trim, actual_trim);
}
