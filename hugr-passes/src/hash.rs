//! Hugr hashing.

use std::hash::{Hash, Hasher};
use hugr_core::ops::{OpTag, OpTrait};
use derive_more::{Display, Error};
use fxhash::{FxHashMap, FxHasher64};
use hugr_core::ops::OpType;
use hugr_core::{HugrView, Node, Hugr};
use hugr_core::hugr::internal::PortgraphNodeMap;
use hugr_core::hugr::internal::HugrInternals;
use petgraph::visit::{self as pg, Walker};




/// Hugr hashing utilities.
pub trait HugrHash {
    /// TODO: FIX THE DOCS
    /// Compute the hash of an hugr object.
    ///
    /// We compute a hash for each node from its operation and the hash of
    /// the predecessors. The hash of the circuit corresponds to the hash of its
    /// output node.
    ///
    /// This hash is independent from the operation traversal order.
    ///
    /// Adapted from Quartz (Apache 2.0)
    /// <https://github.com/quantum-compiler/quartz/blob/2e13eb7ffb3c5c5fe96cf5b4246f4fd7512e111e/src/quartz/tasograph/tasograph.cpp#L410>
    fn hugr_hash(&self, node: Node) -> Result<u64, HashError>;
}

impl<T> HugrHash for T
where
    T: HugrView<Node = Node>, 
{
    fn hugr_hash(&self, node: Node) -> Result<u64, HashError> {
        let node_op = self.get_optype(node);
        if OpTag::DataflowParent.is_superset(node_op.tag()) {
            // In this case, we have a dataflow container
            dfg_hash(self, node)
        } else {
            // otherwise, use generic hash
            generic_hugr_hash(self, node)
        }
    }
}


fn dfg_hash(dfg_hugr: &impl HugrView<Node = Node>, node: Node) -> Result<u64, HashError> {
    println!("Hashing DFG");
    let mut node_hashes = HashState::default();

    let Some([_, output_node]) = dfg_hugr.get_io(node) else {
        return Err(HashError::Unexpected);
    };

    let (region, node_map) = dfg_hugr.region_portgraph(node);
    for pg_node in pg::Topo::new(&region).iter(&region) {
        let node = node_map.from_portgraph(pg_node);
        let hash = hash_node(dfg_hugr, node, &mut node_hashes)?;
        if node_hashes.set_hash(node, hash).is_some() {
            panic!("Hash already set for node {node}");
        }
    }

    node_hashes
        .get_hash(output_node)
        .ok_or(HashError::CyclicDFG)
}

fn generic_hugr_hash(hugr: &impl HugrView<Node = Node>, node: Node) -> Result<u64, HashError> {
    println!("Generic hash called");    
    let mut child_hashes = Vec::new();
    
    for child in hugr.children(node) {
        let mut hasher = FxHasher64::default();
        hugr.hugr_hash(child)?.hash(&mut hasher);
        hashable_op(hugr.get_optype(child)).hash(&mut hasher);
        child_hashes.push(hasher.finish());
    }
    // Combine child hashes using XOR to be order-independent, 
    // looking for a better solution
    Ok(child_hashes.iter().fold(0, |acc, &h| acc ^ h))
}



/// Auxiliary data for circuit hashing.
///
/// Contains previously computed hashes.
// OK!
#[derive(Clone, Default, Debug)]
struct HashState {
    /// Computed node hashes.
    pub hashes: FxHashMap<Node, u64>,
}
// OK!
impl HashState {
    /// Return the hash for a node.
    #[inline]
    fn get_hash(&self, node: Node) -> Option<u64> {
        self.hashes.get(&node).copied()
    }

    /// Register the hash for a node.
    ///
    /// Returns the previous hash, if it was set.
    #[inline]
    fn set_hash(&mut self, node: Node, hash: u64) -> Option<u64> {
        self.hashes.insert(node, hash)
    }
}

/// Returns a hashable representation of an operation.
fn hashable_op(op: &OpType) -> impl Hash + use<> {
    match op {
        OpType::ExtensionOp(op) if !op.args().is_empty() => {
            // TODO: Require hashing for TypeParams?
            format!(
                "{}[{}]",
                op.def().name(),
                serde_json::to_string(op.args()).unwrap()
            )
        }
        OpType::OpaqueOp(op) if !op.args().is_empty() => {
            format!(
                "{}[{}]",
                op.qualified_id(),
                serde_json::to_string(op.args()).unwrap()
            )
        }
        _ => op.to_string(),
    }
}

/// Compute the hash of a circuit command.
///
/// Uses the hash of the operation and the node hash of its predecessors.
///
/// # Panics
/// - If the command is a container node, or if it is a parametric CustomOp.
/// - If the hash of any of its predecessors has not been set.
fn hash_node(
    hugr: &impl HugrView<Node = Node>,
    node: Node,
    state: &mut HashState,
) -> Result<u64, HashError> {
    let op: &OpType = hugr.get_optype(node);
    let mut hasher = FxHasher64::default();

    // Hash the node children
    if hugr.children(node).next().is_some() {
        hugr.hugr_hash(node)?.hash(&mut hasher);
    }

    // Hash the node operation
    hashable_op(op).hash(&mut hasher);

    // Add each each input neighbour hash, including the connected ports.
    // TODO: Ignore state edges?
    for input in hugr.node_inputs(node) {
        // Combine the hash for each subport, ignoring their order.
        let input_hash = hugr
            .linked_ports(node, input)
            .map(|(pred_node, pred_port)| {
                let pred_node_hash = state.get_hash(pred_node);
                fxhash::hash64(&(pred_node_hash, pred_port, input))
            })
            .fold(0, |total, hash| hash ^ total);
        input_hash.hash(&mut hasher);
    }
    Ok(hasher.finish())
}

/// Errors that can occur while hashing a hugr.
#[derive(Debug, Display, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum HashError {
    /// The hugr dfg contains a cycle.
    #[display("The hugr dfg contains a cycle.")]
    CyclicDFG,
    /// Should not happen.
    #[display("An unexpected error occurred during hashing.")]
    Unexpected,
}

#[cfg(test)]
mod  test {
    use crate::utils::test_quantum_extension::{cx_gate, h_gate};
    use crate::utils::{build_simple_hugr};
    use hugr_core::builder::{Dataflow, DataflowSubContainer};
    use std::{fs::File, io::BufReader};

    use super::*;
        #[test]
        fn hash_equality() {

            let hugr1 = build_simple_hugr(
                2,
                |mut f_build| {
                    // let wires = f_build.input_wires().map(Some).collect();

                    let mut linear = f_build.as_circuit(f_build.input_wires());

                    linear
                        .append(h_gate(), [0])?
                        .append(h_gate(), [1])?
                        .append(cx_gate(), [0, 1])?;

                    let outs = linear.finish();
                    f_build.finish_with_outputs(outs)
                },
            ).unwrap();

            let hash1 = hugr1.hugr_hash(hugr1.entrypoint()).unwrap();

            // A circuit built in a different order should have the same hash
            let hugr2 = build_simple_hugr(
            2,
            |mut f_build| {
                let mut linear = f_build.as_circuit(f_build.input_wires());

                linear
                    .append(h_gate(), [1])?
                    .append(h_gate(), [0])?
                    .append(cx_gate(), [0, 1])?;

                let outs = linear.finish();
                f_build.finish_with_outputs(outs)
            },
            ).unwrap();

            let hash2 = hugr2.hugr_hash(hugr2.entrypoint()).unwrap();

            assert_eq!(hash1, hash2);

            // Inverting the CX control and target should produce a different hash
            let hugr3 = build_simple_hugr(
            2,
            |mut f_build| {
                let mut linear = f_build.as_circuit(f_build.input_wires());

                linear
                    .append(h_gate(), [1])?
                    .append(h_gate(), [0])?
                    .append(cx_gate(), [1, 0])?;

                let outs = linear.finish();
                f_build.finish_with_outputs(outs)
            },
            ).unwrap();
            let hash3 = hugr3.hugr_hash(hugr3.entrypoint()).unwrap();

            assert_ne!(hash1, hash3);
        }

        // #[test]
        // fn test_dfg() {
        //     let hugr = build_simple_circuit(
        //         2,|f_build| {
        //             let circ = f_build.as_circuit(f_build.input_wires());

        //         circ.append(h_gate(), [1])?
        //             .append(h_gate(), [0])?
        //             .append(cx_gate(), [1, 0])?;
        //         let outs = circ.finish();
        //         f_build.finish_with_outputs(outs)
        // })
        // .unwrap();
        // }

        fn load_test_files() -> Vec<std::path::PathBuf> {
            let folder_path = concat!(env!("CARGO_MANIFEST_DIR"), "/hugr_hash_test/");

            let mut file_paths = Vec::new();
            for entry in std::fs::read_dir(folder_path).unwrap() {
                let entry = entry.unwrap();
                let path = entry.path();
                if path.extension().and_then(|s| s.to_str()) == Some("hugr") {
                    file_paths.push(path);
                }
            }
            file_paths   
        }

        #[test]
        fn hash_constants_neq() {

            let folder_path = concat!(env!("CARGO_MANIFEST_DIR"), "/hugr_hash_test/");

            let files = [
                "conditional_loop.hugr",
                "const_op.hugr",
                "empty_func.hugr",
                // "fn_calls.hugr",
                "loop_conditional.hugr",
                "one_rz.hugr",
                "repeat_until_success.hugr",
            ];

            // for file_path in load_test_files() {
            //     let entry = entry.unwrap();
            //     let path = entry.path();
            //     print!("1. Loading file: {:?}\n", path);
            //     if path.extension().and_then(|s| s.to_str()) == Some("hugr") {
            //     let file = File::open(&path).unwrap();
            //     let hugr = Hugr::load(BufReader::new(file), None).unwrap();
            //     all_hashes.push(hugr.hugr_hash(hugr.entrypoint()).unwrap());
            //     }
            // }

            let mut all_hashes = Vec::new();
            for entry in files {
                let file_path = format!("{}{}", folder_path, entry);
                let file = File::open(&file_path).unwrap();
                let hugr = Hugr::load(BufReader::new(file), None);
                let hugr = hugr.unwrap();
                let hash = hugr.hugr_hash(hugr.entrypoint()).unwrap();
                println!("Testing: {}, Hash: {}\n", entry, hash);
                all_hashes.push(hash);
            }
            
            let set: std::collections::HashSet<u64> = all_hashes.iter().copied().collect();
            // check that all hashes are different
            assert_eq!(set.len(), all_hashes.len()); // fail due to hash(one_rz.hugr) == hash(fn_calls.hugr)
        }
    

        #[test]
        fn hash_idempotency_on_files() {
  
            for file_path in load_test_files() {
                // First hash computation
                let file1 = File::open(&file_path).unwrap();
                let hugr1 = Hugr::load(BufReader::new(file1), None).unwrap();
                let hash1 = hugr1.hugr_hash(hugr1.entrypoint()).unwrap();

                // Second hash computation
                let file2 = File::open(&file_path).unwrap();
                let hugr2 = Hugr::load(BufReader::new(file2), None).unwrap();
                let hash2 = hugr2.hugr_hash(hugr2.entrypoint()).unwrap();
                assert_eq!(hash1, hash2, "Hash is not idempotent for file: {}", file_path.display());
            }
        }
}