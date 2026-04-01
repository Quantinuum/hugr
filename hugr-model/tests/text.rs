#![allow(missing_docs)]

use hugr_core::{Hugr, HugrView};
use hugr_model::v0::ast;
use rstest::rstest;
use std::str::FromStr as _;

fn envelope_parse(source: &mut String) -> Result<(), anyhow::Error> {
    source.insert_str(0, "HUGRiHJv(@");
    let hugr = Hugr::load_str(source, None)?;
    hugr.validate()?;
    Ok(())
}

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
    {
        let mut s: String = expected.to_string();
        envelope_parse(&mut s)?;
    }
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
