//! Hugr hashing.

use derive_more::{Display, Error};
use fxhash::{FxHashMap, FxHasher64};
use hugr_core::HugrView;
use hugr_core::hugr::internal::PortgraphNodeMap;
use hugr_core::ops::OpType;
use hugr_core::ops::{OpTag, OpTrait};
use petgraph::visit::{self as pg, Walker};
use std::hash::{Hash, Hasher};

/// Hugr hashing utilities.
pub trait HugrHash: HugrView {
    /// Compute a hash for the entire HUGR structure.
    ///
    /// This corresponds to the hash of the root node.
    fn hugr_hash(&self) -> Result<u64, HashError> {
        self.region_hash(self.module_root())
    }

    /// Compute a hash for a hugr region.
    ///
    /// If the hugr is a dfg, we compute a hash for each node from its operation
    /// and the hash of the predecessors. The hash of the hugr corresponds to
    /// the hash of its output node.
    /// Otherwise, we compute a generic hash combining the hashes of its children.
    ///
    /// This hash is independent from the children node order.
    fn region_hash(&self, node: Self::Node) -> Result<u64, HashError>;
}

impl<H: HugrView> HugrHash for H {
    fn region_hash(&self, node: Self::Node) -> Result<u64, HashError> {
        let node_op = self.get_optype(node);
        let mut hasher = FxHasher64::default();

        let op: &OpType = self.get_optype(node);
        hashable_op(op).hash(&mut hasher);

        if OpTag::DataflowParent.is_superset(node_op.tag()) {
            // In this case, we have a dataflow container
            dfg_hash(self, node)?.hash(&mut hasher);
        } else {
            // otherwise, use generic hash
            generic_hugr_hash(self, node)?.hash(&mut hasher);
        }

        Ok(hasher.finish())
    }
}

fn dfg_hash<H: HugrView>(dfg_hugr: &H, node: H::Node) -> Result<u64, HashError> {
    let mut node_hashes = HashState {
        hashes: FxHashMap::default(),
    };

    let [_, output_node] = dfg_hugr.get_io(node).expect("DFG region missing I/O nodes");

    let (region, node_map) = dfg_hugr.region_portgraph(node);
    for pg_node in pg::Topo::new(&region).iter(&region) {
        let child = node_map.from_portgraph(pg_node);
        let hash = dfg_hash_node(dfg_hugr, child, &mut node_hashes)?;
        if node_hashes.set_hash(child, hash).is_some() {
            panic!("Hash already set for node {node}");
        }
    }

    node_hashes
        .get_hash(output_node)
        .ok_or(HashError::CyclicDFG)
}

fn generic_hugr_hash<H: HugrView>(hugr: &H, node: H::Node) -> Result<u64, HashError> {
    let mut child_hashes = Vec::new();

    for child in hugr.children(node) {
        child_hashes.push(hugr.region_hash(child)?);
    }
    // Combine child hashes in an order-independent way
    child_hashes.sort_unstable();
    Ok(fxhash::hash64(&child_hashes))
}

/// Auxiliary data for circuit hashing.
///
/// Contains previously computed hashes.
#[derive(Clone, Default, Debug)]
struct HashState<H: HugrView> {
    /// Computed node hashes.
    pub hashes: FxHashMap<H::Node, u64>,
}
impl<H: HugrView> HashState<H> {
    /// Return the hash for a node.
    #[inline]
    fn get_hash(&self, node: H::Node) -> Option<u64> {
        self.hashes.get(&node).copied()
    }

    /// Register the hash for a node.
    ///
    /// Returns the previous hash, if it was set.
    #[inline]
    fn set_hash(&mut self, node: H::Node, hash: u64) -> Option<u64> {
        self.hashes.insert(node, hash)
    }
}

/// Returns a hashable representation of an operation.
///
/// TODO(perf): String formatting here is a big bottleneck
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
fn dfg_hash_node<H: HugrView>(
    hugr: &H,
    node: H::Node,
    state: &mut HashState<H>,
) -> Result<u64, HashError> {
    let mut hasher = FxHasher64::default();

    hugr.region_hash(node)?.hash(&mut hasher);

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
}

#[cfg(test)]
mod test {
    use crate::utils::build_simple_hugr;
    use crate::utils::test_quantum_extension::{cx_gate, h_gate};
    use hugr_core::builder::{Dataflow, DataflowSubContainer};

    use super::*;
    #[test]
    fn hash_equality() {
        let hugr1 = build_simple_hugr(2, |mut f_build| {
            // let wires = f_build.input_wires().map(Some).collect();

            let mut linear = f_build.as_circuit(f_build.input_wires());

            linear
                .append(h_gate(), [0])?
                .append(h_gate(), [1])?
                .append(cx_gate(), [0, 1])?;

            let outs = linear.finish();
            f_build.finish_with_outputs(outs)
        })
        .unwrap();

        let hash1 = hugr1.hugr_hash().unwrap();

        // A circuit built in a different order should have the same hash
        let hugr2 = build_simple_hugr(2, |mut f_build| {
            let mut linear = f_build.as_circuit(f_build.input_wires());

            linear
                .append(h_gate(), [1])?
                .append(h_gate(), [0])?
                .append(cx_gate(), [0, 1])?;

            let outs = linear.finish();
            f_build.finish_with_outputs(outs)
        })
        .unwrap();

        let hash2 = hugr2.hugr_hash().unwrap();

        assert_eq!(hash1, hash2);

        // Inverting the CX control and target should produce a different hash
        let hugr3 = build_simple_hugr(2, |mut f_build| {
            let mut linear = f_build.as_circuit(f_build.input_wires());

            linear
                .append(h_gate(), [1])?
                .append(h_gate(), [0])?
                .append(cx_gate(), [1, 0])?;

            let outs = linear.finish();
            f_build.finish_with_outputs(outs)
        })
        .unwrap();
        let hash3 = hugr3.hugr_hash().unwrap();

        assert_ne!(hash1, hash3);
    }
}
