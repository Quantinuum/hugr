#![allow(missing_docs)]

use hugr_model::v0::ast;
use hugr_model::v0::{SymbolName, Visibility};
use rstest::rstest;
use std::str::FromStr as _;

fn roundtrip(source: &str) -> String {
    let package = ast::Package::from_str(source).unwrap();
    package.to_string()
}

#[rstest]
#[cfg_attr(miri, ignore)] // Opening files is not supported in (isolated) miri
pub fn test_roundtrip(
    #[files("tests/fixtures/*.edn")]
    #[mode = str]
    expected: &str,
) -> Result<(), anyhow::Error> {
    let actual = roundtrip(expected);
    // Trim whitespace from the strings to compare them
    let expected_trim = expected
        .split_whitespace()
        .fold(String::new(), |acc, s| acc + s);
    let actual_trim = actual
        .split_whitespace()
        .fold(String::new(), |acc, s| acc + s);
    assert_eq!(expected_trim, actual_trim);
    Ok(())
}

#[rstest]
#[case::locals("tests.integration.test_basic.test_implicit_return.<locals>.ret")]
#[case::dollar("example.foo$bar")]
#[case::ampersand("example.foo&bar")]
#[case::brackets("example.foo[T]")]
#[case::comma_space("example.foo, bar")]
#[case::reserved("mod")]
#[case::raw_delimiter("example.foo\"#bar")]
pub fn test_symbol_name_roundtrip(#[case] name: &str) {
    let symbol = ast::Symbol {
        visibility: Some(Visibility::Public),
        name: SymbolName::new(name),
        version: None,
        params: Box::default(),
        constraints: Box::default(),
        signature: ast::Term::from_str("(core.fn [] [])").unwrap(),
    };

    let source = symbol.to_string();
    let parsed = ast::Symbol::from_str(&source).unwrap();

    assert_eq!(parsed, symbol);
}

#[rstest]
#[case::locals("tests.integration.test_basic.test_implicit_return.<locals>.ret")]
#[case::comma_space("example.foo, bar")]
pub fn test_package_symbol_name_roundtrip(#[case] name: &str) {
    let source = format!(
        r##"(hugr 0)

(mod)

(import core.fn)

(declare-func public r#"{name}"# (core.fn [] []))

(r#"{name}"# [] []
  (signature (core.fn [] [])))
"##
    );

    let roundtripped = roundtrip(&source);
    let parsed = ast::Package::from_str(&roundtripped).unwrap();

    assert_eq!(parsed.to_string(), roundtripped);
}

#[rstest]
fn test_raw_symbol_name_in_term() {
    let term = ast::Term::from_str(r##"r#"example.foo<bar>"#"##).unwrap();

    assert_eq!(
        term,
        ast::Term::Apply(
            ast::SymbolIdent {
                name: SymbolName::new("example.foo<bar>"),
                version: None,
            },
            [].into(),
        )
    );
}

/// Parsing an invalid s-expression symbol definition should fail.
///
/// Non-supported characters like `<` and `>` are not allowed in bare symbol names,
/// they require escaping with the raw symbol syntax.
#[rstest]
fn test_symbol_name_rejects_partial_parse() {
    let name = "tests.integration.test_linear.test_return_call.<locals>.op";

    assert!(ast::SymbolIdent::from_str(name).is_err());
    assert!(ast::Term::from_str(name).is_err());
}
