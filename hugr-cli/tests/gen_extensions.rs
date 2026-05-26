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
fn test_extension_dump(mut cmd: Command) {
    let temp_dir = assert_fs::TempDir::new()
        .expect("temp dir creation failure.")
        .into_persistent_if(std::env::var_os("HUGR_CLI_TEST_PERSIST_FILES").is_some());
    cmd.arg("-o");
    cmd.arg(temp_dir.path());
    cmd.assert().success();

    let expected_paths = BTreeSet::from(
        [
            "logic.json",
            "prelude.json",
            "ptr.json",
            "arithmetic/int/types.json",
            "arithmetic/float/types.json",
            "arithmetic/int.json",
            "arithmetic/float.json",
            "arithmetic/conversions.json",
            "collections/array.json",
            "collections/borrow_arr.json",
            "collections/list.json",
            "collections/static_array.json",
        ]
        .map(std::path::PathBuf::from),
    );

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

#[rstest]
fn test_extension_versioned_dump(mut cmd: Command) {
    let temp_dir = assert_fs::TempDir::new()
        .expect("temp dir creation failure.")
        .into_persistent_if(std::env::var_os("HUGR_CLI_TEST_PERSIST_FILES").is_some());
    cmd.arg("-o");
    cmd.arg(temp_dir.path());
    cmd.arg("--versioned");
    cmd.assert().success();

    let expected_paths = [
        "logic-0.1.0.json",
        "prelude-0.2.2.json",
        "ptr-0.1.1.json",
        "arithmetic/int/types-0.1.0.json",
        "arithmetic/float/types-0.1.0.json",
        "arithmetic/int-0.1.1.json",
        "arithmetic/float-0.1.1.json",
        "arithmetic/conversions-0.1.1.json",
        "collections/array-0.1.2.json",
        "collections/borrow_arr-0.2.1.json",
        "collections/list-0.1.1.json",
        "collections/static_array-0.1.1.json",
    ];
    // check all paths exist
    for path in &expected_paths {
        let full_path = temp_dir.join(path);
        assert!(full_path.exists());
    }

    // temp dir deleted when dropped here
}
