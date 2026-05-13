#![allow(missing_docs)]

use hugr_model::v0::ast;
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
