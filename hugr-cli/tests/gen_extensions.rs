//! Tests for the CLI extension writing.
//!
//! Miri is globally disabled for these tests because they mostly involve
//! calling the CLI binary, which Miri doesn't support.
#![cfg(all(test, not(miri)))]

use std::collections::BTreeSet;

use assert_cmd::Command;
use rstest::{fixture, rstest};
use walkdir::WalkDir;

#[fixture]
fn cmd() -> Command {
    let mut cmd = assert_cmd::cargo::cargo_bin_cmd!("hugr");
    cmd.arg("gen-extensions");
    cmd
}

#[rstest]
#[case::versioned(false)]
#[case::unversioned(true)]
fn test_extension_dump(mut cmd: Command, #[case] unversioned: bool) {
    let temp_dir = assert_fs::TempDir::new()
        .expect("temp dir creation failure.")
        .into_persistent_if(std::env::var_os("HUGR_CLI_TEST_PERSIST_FILES").is_some());
    cmd.arg("-o");
    cmd.arg(temp_dir.path());
    if unversioned {
        cmd.arg("--unversioned");
    }
    cmd.assert().success();

    let expected_paths = hugr::std_extensions::STD_REG
        .iter()
        .map(|ext| {
            let mut path = ext.id().replace('.', "/");
            if unversioned {
                path.push_str(".json");
            } else {
                path.push_str(&format!("-{}.json", ext.latest().version()));
            }
            std::path::PathBuf::from(path)
        })
        .collect::<BTreeSet<_>>();

    let existing_paths = WalkDir::new(&temp_dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
        .map(|e| e.path().strip_prefix(&temp_dir).unwrap().to_owned())
        .collect::<BTreeSet<_>>();

    // Check differences and print any missing or unexpected paths.
    if expected_paths != existing_paths {
        let missing_paths: Vec<_> = expected_paths.difference(&existing_paths).collect();
        let unexpected_paths: Vec<_> = existing_paths.difference(&expected_paths).collect();

        if !missing_paths.is_empty() {
            eprintln!("Missing paths:");
            for path in missing_paths {
                eprintln!("  {}", path.display());
            }
        }

        if !unexpected_paths.is_empty() {
            eprintln!("Unexpected paths:");
            for path in unexpected_paths {
                eprintln!("  {}", path.display());
            }
        }
        panic!("Extension dump did not match expected paths.");
    }

    // temp dir deleted when dropped here
}
