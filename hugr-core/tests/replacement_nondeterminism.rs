//! Regression test for deterministic node reuse after an identical replacement.

use std::collections::BTreeSet;

use hugr_core::hugr::hugrmut::HugrMut;
use hugr_core::hugr::patch::replace::Replacement;
use hugr_core::ops::{Const, constant::Value};
use hugr_core::{Hugr, HugrView};

#[test]
fn replacement_node_reuse_is_deterministic() {
    let mut original = Hugr::new();
    let root = original.module_root();
    let constant = Const::new(Value::true_val());
    let a = original.add_node_with_parent(root, constant.clone());
    let b = original.add_node_with_parent(root, constant.clone());
    original.validate().unwrap();

    let replacement = Replacement {
        removal: vec![a, b],
        replacement: Hugr::new(),
        adoptions: Default::default(),
        mu_inp: vec![],
        mu_out: vec![],
        mu_new: vec![],
    };
    let mut allocated = BTreeSet::new();
    for _ in 0..64 {
        let mut h = original.clone();
        h.apply_patch(replacement.clone()).unwrap();
        h.validate().unwrap();
        // This is a fresh allocation, not a dereference of a removed node.
        allocated.insert(h.add_node_with_parent(root, constant.clone()));
        h.validate().unwrap();
    }
    assert_eq!(
        allocated.len(),
        1,
        "Identical operations allocated different node IDs: {allocated:?}"
    );
}
