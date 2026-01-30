//! Circuit hashing.

use std::hash::{Hash, Hasher};

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

impl HugrHash for Hugr {
    fn hugr_hash(&self, node: Node) -> Result<u64, HashError> {

        match self.get_io(node) {
            Some([_, output_node]) => {
                // In this case, we have a dataflow container
                dfg_hash(self, node, output_node)
                
            }
            Option::None => {
                // otherwise, use generic hash
                generic_hugr_hash(self, node)
            }
        }
    }
}


fn dfg_hash(dfg_hugr:&Hugr, node: Node, output_node: Node) -> Result<u64, HashError> {
    println!("Hashing DFG");
    let mut node_hashes = HashState::default();

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
        .ok_or(HashError::CyclicCircuit)
}

fn generic_hugr_hash(hugr: &Hugr, node: Node) -> Result<u64, HashError> {
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
    hugr: &Hugr,
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
    /// The circuit contains a cycle.
    #[display("The circuit contains a cycle.")]
    CyclicCircuit,
    /// The hashed hugr is not a DFG.
    #[display("Tried to hash a non-dfg hugr.")]
    NotADfg,
    /// Should not happen.
    #[display("An unexpected error occurred during hashing.")]
    Unexpected,
}

#[cfg(test)]
mod test {
    // use crate::utils::test_quantum_extension::{cx_gate, h_gate};
    // use crate::utils::build_simple_hugr;
    // use hugr_core::builder::{Dataflow, DataflowSubContainer};
    // use std::{fs::File, io::BufReader};

    // use super::*;
//     #[test]
//     fn hash_equality() {
        
        
//         let hugr1 = build_simple_hugr(
//             2,
//             |mut f_build| {
//                 // let wires = f_build.input_wires().map(Some).collect();

//                 let mut linear = f_build.as_circuit(f_build.input_wires());
                
//                 // CircuitBuilder {
//                 //     wires,
//                 //     builder: &mut f_build,
//                 // };

//                 assert_eq!(linear.n_wires(), 2);

//                 linear
//                     .append(h_gate(), [0])?
//                     .append(h_gate(), [1])?
//                     .append(cx_gate(), [0, 1])?;

//                 let outs = linear.finish();
//                 f_build.finish_with_outputs(outs)
//             },
//         ).unwrap();
 
//         let hash1 = hugr1.circuit_hash(hugr1.entrypoint()).unwrap();

//         // A circuit built in a different order should have the same hash
//         let hugr2 = build_simple_hugr(
//         2,
//         |mut f_build| {
//             let mut linear = f_build.as_circuit(f_build.input_wires());

//             assert_eq!(linear.n_wires(), 2);

//             linear
//                 .append(h_gate(), [1])?
//                 .append(h_gate(), [0])?
//                 .append(cx_gate(), [0, 1])?;

//             let outs = linear.finish();
//             f_build.finish_with_outputs(outs)
//         },
//         ).unwrap();
        
//         let hash2 = hugr2.circuit_hash(hugr2.entrypoint()).unwrap();

//         assert_eq!(hash1, hash2);

//         // Inverting the CX control and target should produce a different hash
//         let hugr3 = build_simple_hugr(
//         2,
//         |mut f_build| {

//             let mut linear = f_build.as_circuit(f_build.input_wires());

//             assert_eq!(linear.n_wires(), 2);

//             linear
//                 .append(h_gate(), [1])?
//                 .append(h_gate(), [0])?
//                 .append(cx_gate(), [1, 0])?;

//             let outs = linear.finish();
//             f_build.finish_with_outputs(outs)
//         },
//         ).unwrap();
//         let hash3 = hugr3.circuit_hash(hugr3.entrypoint()).unwrap();

//         assert_ne!(hash1, hash3);
//     }

//     // #[test]
//     // fn hash_constants() {
//     //     let c_str = r#"{"bits": [], "commands": [{"args": [["q", [0]]], "op": {"params": ["0.5"], "type": "Rz"}}], "created_qubits": [], "discarded_qubits": [], "implicit_permutation": [[["q", [0]], ["q", [0]]]], "phase": "0.0", "qubits": [["q", [0]]]}"#;
//     //     let ser: circuit_json::SerialCircuit = serde_json::from_str(c_str).unwrap();
//     //     let circ: Circuit = ser.decode(DecodeOptions::new()).unwrap();
//     //     circ.circuit_hash(circ.parent()).unwrap();
//     // }

//     #[test]
//     fn hash_constants_neq() {

//         let folder_path = concat!(env!("CARGO_MANIFEST_DIR"), "/hugr_hash_test/");

//         let files = [
//             "conditional_loop.hugr",
//             "const_op.hugr",
//             "empty_func.hugr",
//             "fn_calls.hugr",
//             "loop_conditional.hugr",
//             "one_rz.hugr",
//             "repeat_until_success.hugr",
//         ];

//         // let mut hugrs = Vec::new();
//         // for entry in std::fs::read_dir(folder_path).unwrap() {
//         //     let entry = entry.unwrap();
//         //     let path = entry.path();
//         //     print!("1. Loading file: {:?}\n", path);
//         //     if path.extension().and_then(|s| s.to_str()) == Some("hugr") {
//         //     let file = File::open(&path).unwrap();
//         //     let hugr = Hugr::load(BufReader::new(file), None).unwrap();
//         //     hugrs.push(hugr);
//         //     }
//         // }

//         let mut hugrs = Vec::new();
//         for entry in files {
//             let file_path = format!("{}{}", folder_path, entry);
//             print!("Loading file: {}\n", entry);
//             let file = File::open(&file_path).unwrap();
//             let hugr = Hugr::load(BufReader::new(file), None);
//             let hugr = hugr.unwrap();
//             hugrs.push(hugr);
//         }
        
        
        
//         let mut all_hashes = Vec::new();

//         for hugr in &hugrs {
//             all_hashes.push(hugr.circuit_hash(hugr.entrypoint()).unwrap());
//         }
        
//         let set: std::collections::HashSet<u64> = all_hashes.iter().copied().collect();
//         // check that all hashes are different
//         assert_eq!(set.len(), all_hashes.len());
        
//         // for c_str in [c_str1, c_str2] {
//         //     let ser: circuit_json::SerialCircuit = serde_json::from_str(c_str).unwrap();
//         //     let circ: Circuit = ser.decode(DecodeOptions::new()).unwrap();
//         //     all_hashes.push(circ.circuit_hash(circ.parent()).unwrap());
//         // }
//         // assert_ne!(all_hashes[0], all_hashes[1]);
//     }
// 
}
