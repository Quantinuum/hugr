use crate::builder::{DFGBuilder, Dataflow, DataflowHugr};
use crate::hugr::serialize::test::{HugrDeser, HugrSer};
use crate::hugr::test::check_hugr_equality;
use crate::{
    HugrView as _, extension::prelude::bool_t, std_extensions::logic::LogicOp, types::Signature,
};
use std::{
    fs::OpenOptions,
    path::{Path, PathBuf},
    sync::LazyLock,
};

use crate::Hugr;
use rstest::{fixture, rstest};

static TEST_CASE_DIR: LazyLock<PathBuf> = LazyLock::new(|| {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join(file!())
        .parent()
        .unwrap()
        .join("testcases")
});

#[test]
fn test_case_dir_exists() {
    let test_case_dir: &Path = &TEST_CASE_DIR;
    assert!(
        test_case_dir.exists(),
        "Upgrade test case directory does not exist: {test_case_dir:?}"
    );
}

#[fixture]
#[once]
pub fn empty_hugr() -> Hugr {
    Hugr::default()
}

#[fixture]
#[once]
pub fn hugr_with_named_op() -> Hugr {
    let mut builder =
        DFGBuilder::new(Signature::new(vec![bool_t(), bool_t()], vec![bool_t()])).unwrap();
    let [a, b] = builder.input_wires_arr();
    let x = builder.add_dataflow_op(LogicOp::And, [a, b]).unwrap();
    builder.finish_hugr_with_outputs(x.outputs()).unwrap()
}

#[rstest]
#[case("empty_hugr", empty_hugr())]
#[case("hugr_with_named_op", hugr_with_named_op())]
fn serial_upgrade(#[case] name: String, #[case] hugr: Hugr) {
    let path = TEST_CASE_DIR.join(format!("{name}.json"));
    if !path.exists() {
        let f = OpenOptions::new()
            .create(true)
            .truncate(true)
            .write(true)
            .open(&path)
            .unwrap();
        serde_json::to_writer_pretty(f, &HugrSer(&hugr)).unwrap();
    }

    // we do not expect `val` to satisfy any schemas, it is a non-latest
    // version.
    let val = serde_json::from_reader(std::fs::File::open(&path).unwrap()).unwrap();

    // We need to resolve extensions and correctly set the extension versions
    // before checking for equality.
    let mut new_hugr: HugrDeser = serde_json::from_value(val).unwrap();
    new_hugr
        .0
        .resolve_extension_defs(hugr.extensions())
        .unwrap();

    check_hugr_equality(&hugr, &new_hugr.0);
}
