//! A pass for removing redundant order edges in a Hugr region.

use std::collections::{HashMap, HashSet, VecDeque};

use hugr_core::core::HugrNode;
use hugr_core::hugr::internal::PortgraphNodeMap;
use hugr_core::hugr::{HugrError, hugrmut::HugrMut};
use hugr_core::ops::{OpTag, OpTrait};
use hugr_core::{HugrView, IncomingPort, Node, OutgoingPort};
use itertools::Itertools;
use petgraph::visit::Walker;

use crate::ComposablePass;

/// A pass for removing order edges in a Hugr region that are already implied by
/// other order or dataflow dependencies.
///
/// Ignores order edges to region parents, as they may be required for keeping
/// external edges valid.
///
/// Each evaluation on a region runs in `O(e + n log(n) * #order_edges)` time,
/// where `e` and `n` are the number of edges and nodes in the region,
/// respectively.
#[derive(Default, Debug, Clone, Copy)]
pub struct RedundantOrderEdgesPass {
    /// Whether to traverse the HUGR recursively.
    recursive: bool,
}

/// Result type for the redundant order edges pass.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, derive_more::AddAssign)]
pub struct RedundantOrderEdgesResult {
    /// Number of edges removed.
    pub edges_removed: usize,
}

impl RedundantOrderEdgesPass {
    /// Create a new redundant order edges pass with the given configuration.
    pub fn new() -> Self {
        Self { recursive: true }
    }

    /// Sets whether the pass should traverse the HUGR recursively.
    pub fn recursive(mut self, recursive: bool) -> Self {
        self.recursive = recursive;
        self
    }

    /// Evaluate the pass on the given dataflow region.
    ///
    /// # Arguments
    ///
    /// * `hugr`: The hugr to evaluate the pass on.
    /// * `region`: The region to evaluate the pass on.
    /// * `region_candidates`: A queue of nodes to explore in the region. If
    ///   `self.recursive`, we will add to this list any children nodes of the
    ///   region.
    pub fn run_on_df_region<H: HugrMut>(
        &self,
        hugr: &mut H,
        parent: H::Node,
        region_candidates: &mut VecDeque<H::Node>,
    ) -> Result<RedundantOrderEdgesResult, HugrError> {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        struct PredecessorOrderEdges<N: HugrNode> {
            from_node: N,
            from_port: OutgoingPort,
            to_node: N,
            to_port: IncomingPort,
        }

        // A map with order edges that originate from predecessors of each node.
        // We only store this for nodes that will be visited next (i.e. unexplored neighbors of explored nodes).
        let mut predecessor_order_edges: HashMap<H::Node, HashSet<PredecessorOrderEdges<H::Node>>> =
            HashMap::new();
        // Order edges to be removed.
        let mut to_remove = Vec::new();

        // Traverse the region in topological order.
        let (region, node_map) = hugr.region_portgraph(parent);
        let postorder = petgraph::visit::Topo::new(&region);
        for pg_node in postorder.iter(&region) {
            let node = node_map.from_portgraph(pg_node);
            let op = hugr.get_optype(node);

            // If the node has children and we are running recursively, add the children to the region candidates.
            if self.recursive && hugr.first_child(node).is_some() {
                region_candidates.extend(hugr.children(node));
            }

            let predecessor_edges = predecessor_order_edges.remove(&node).unwrap_or_default();

            // If we have reached the target of an order edge by exploring
            // connected nodes from the source, then mark the order edge for
            // removal.
            let removable_edges: HashSet<PredecessorOrderEdges<H::Node>> = predecessor_edges
                .iter()
                .filter(|edge| edge.to_node == node)
                .copied()
                .collect();

            // Remove the removable edges from the set of predecessor edges we'll pass to the forward neighbors.
            let predecessor_edges: HashSet<PredecessorOrderEdges<H::Node>> = predecessor_edges
                .difference(&removable_edges)
                .copied()
                .collect();

            // Collect the order edges originating from this node that do not lead to a node with children.
            //
            // The latter may be necessary for keeping external edges valid.
            let new_edges = match op.other_output_port() {
                Some(out_order_port) => hugr
                    .linked_inputs(node, out_order_port)
                    .filter(|(to_node, _)| {
                        hugr.get_parent(*to_node) == Some(parent)
                            && hugr.first_child(*to_node).is_none()
                    })
                    .map(|(to_node, to_port)| PredecessorOrderEdges {
                        from_node: node,
                        from_port: out_order_port,
                        to_node,
                        to_port,
                    })
                    .collect_vec(),
                None => vec![],
            };

            // Add the order edges to the `predecessor_order_edges` of the forward neighbors of the node.
            for out_port in op.value_output_ports().chain(op.static_output_port()) {
                for (to_node, _) in hugr.linked_inputs(node, out_port) {
                    if hugr.get_parent(to_node) != Some(parent) {
                        continue;
                    }
                    let neigh_predecessor_order_edges =
                        predecessor_order_edges.entry(to_node).or_default();
                    neigh_predecessor_order_edges.extend(predecessor_edges.clone());
                    neigh_predecessor_order_edges.extend(new_edges.clone());
                }
            }
            // Do not propagate new order edges through themselves (otherwise we'd always remove them).
            if let Some(out_port) = op.other_output_port() {
                for (to_node, _) in hugr.linked_inputs(node, out_port) {
                    if hugr.get_parent(to_node) != Some(parent) {
                        continue;
                    }
                    let neigh_predecessor_order_edges =
                        predecessor_order_edges.entry(to_node).or_default();
                    neigh_predecessor_order_edges.extend(predecessor_edges.clone());
                }
            }

            to_remove.extend(removable_edges);
        }
        // Release the hugr borrow so we can mutate it.
        drop(region);
        let edges_removed = to_remove.len();

        for edge in to_remove {
            hugr.disconnect_edge(edge.from_node, edge.from_port, edge.to_node, edge.to_port);
        }

        Ok(RedundantOrderEdgesResult { edges_removed })
    }
}

impl<H: HugrMut<Node = Node>> ComposablePass<H> for RedundantOrderEdgesPass {
    type Error = HugrError;
    type Result = RedundantOrderEdgesResult;

    fn run(&self, hugr: &mut H) -> Result<Self::Result, Self::Error> {
        // Nodes to explore in the hugr.
        let mut region_candidates = VecDeque::from_iter([hugr.entrypoint()]);
        let mut result = RedundantOrderEdgesResult::default();

        while let Some(region) = region_candidates.pop_front() {
            let op = hugr.get_optype(region);

            if OpTag::DataflowParent.is_superset(op.tag()) {
                result += self.run_on_df_region(hugr, region, &mut region_candidates)?;
            } else {
                // When exploring non-dataflow regions, add the children recursively (independently of self.recursive).
                region_candidates.extend(hugr.children(region));
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use hugr_core::builder::{Dataflow, DataflowHugr, FunctionBuilder, SubContainer};
    use hugr_core::extension::prelude::{Noop, bool_t};
    use hugr_core::ops::handle::NodeHandle;
    use hugr_core::types::Signature;

    use super::*;

    /// Construct a simple hugr with a bunch of noops
    ///
    /// ```
    /// input -> noop1 --> noop2 --> noop3 -> nested_op
    ///       |
    ///       v
    ///       noop4 --> noop5 --> output
    /// ```
    ///
    /// With order edges
    /// - input -> noop2
    /// - noop1 -> output
    /// - noop4 -> noop3
    /// - noop5 -> noop2
    /// - noop3 -> nested_op
    ///
    /// After running the pass, only the following order edges should remain:
    /// - noop1 -> output
    /// - noop5 -> noop2
    /// - noop3 -> nested_op
    #[test]
    fn test_redundant_order_edges() {
        let mut hugr = FunctionBuilder::new("f", Signature::new_endo([bool_t()])).unwrap();
        let op = Noop::new(bool_t());

        let [input, output] = hugr.io();
        let [b1] = hugr.input_wires_arr();
        let noop1 = hugr.add_dataflow_op(Noop::new(bool_t()), [b1]).unwrap();
        let noop2 = hugr
            .add_dataflow_op(op.clone(), [noop1.out_wire(0)])
            .unwrap();
        let noop3 = hugr
            .add_dataflow_op(op.clone(), [noop2.out_wire(0)])
            .unwrap();
        let noop4 = hugr.add_dataflow_op(op.clone(), [b1]).unwrap();
        let noop5 = hugr
            .add_dataflow_op(op.clone(), [noop4.out_wire(0)])
            .unwrap();
        let nested_op = hugr
            .dfg_builder(Signature::new(vec![bool_t()], vec![]), [noop5.out_wire(0)])
            .unwrap()
            .finish_sub_container()
            .unwrap();

        // Set the order edges as described in the test description.
        hugr.set_order(&input, &noop2);
        hugr.set_order(&noop1, &output);
        hugr.set_order(&noop4, &noop3);
        hugr.set_order(&noop5, &noop2);
        hugr.set_order(&noop3, &nested_op.node());

        let mut hugr = hugr.finish_hugr_with_outputs([noop5.out_wire(0)]).unwrap();

        // Run the pass
        let result = RedundantOrderEdgesPass::new().run(&mut hugr).unwrap();
        assert_eq!(result.edges_removed, 2);

        // Check that we removed the correct order edges.
        // We know all order edge ports here will have the same index, since we are using the same op types.
        let order_in = IncomingPort::from(1);
        let order_out = OutgoingPort::from(1);
        assert_eq!(hugr.single_linked_input(input, order_out), None);
        assert_eq!(
            hugr.single_linked_input(noop1.node(), order_out),
            Some((output, order_in))
        );
        assert_eq!(hugr.single_linked_input(noop4.node(), order_out), None);
        assert_eq!(
            hugr.single_linked_input(noop5.node(), order_out),
            Some((noop2.node(), order_in))
        );
        assert_eq!(
            hugr.single_linked_input(noop3.node(), order_out),
            Some((nested_op.node(), order_in))
        );
    }
}
