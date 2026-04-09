use petgraph::visit::{
    GraphBase, IntoNeighborsDirected, IntoNodeIdentifiers, NodeCount, Topo, Visitable, Walker,
};
use std::collections::BTreeSet;

use portgraph::{SecondaryMap, UnmanagedDenseMap};

/// Convexity checking using a pre-computed topological node order.
pub(super) struct TopoConvexChecker<G: GraphBase> {
    graph: G,
    // The nodes in topological order
    topsort_nodes: Vec<G::NodeId>,
    // The index of a node in the topological order (the inverse of topsort_nodes)
    topsort_ind: UnmanagedDenseMap<G::NodeId, usize>,
}

impl<G: NodeCount> TopoConvexChecker<G>
where
    for<'a> &'a G: IntoNeighborsDirected + IntoNodeIdentifiers + Visitable<NodeId = G::NodeId>,
    G::NodeId: Into<usize> + TryFrom<usize> + Copy,
{
    /// Create a new ConvexChecker.
    pub fn new(graph: G) -> Self {
        let topsort_nodes: Vec<_> = Topo::new(&graph).iter(&graph).collect();
        let mut topsort_ind = UnmanagedDenseMap::with_capacity(graph.node_count());
        for (i, &n) in topsort_nodes.iter().enumerate() {
            topsort_ind.set(n, i);
        }
        Self {
            graph,
            topsort_nodes,
            topsort_ind,
        }
    }

    /// The graph on which convexity queries can be made.
    pub fn graph(&self) -> &G {
        &self.graph
    }

    /// Whether the subgraph induced by the node set is convex.
    ///
    /// An induced subgraph is convex if there is no node that is both in the
    /// past and in the future of some nodes in the subgraph.
    ///
    /// ## Arguments
    ///
    /// - `nodes`: The nodes inducing a subgraph of `self.graph()`.
    ///
    /// ## Algorithm
    ///
    /// Each node in the "vicinity" of the subgraph will be assigned a causal
    /// property, either of being in the past or in the future of the subgraph.
    /// It can then be checked whether there is a node in the past that is also
    /// in the future, violating convexity.
    ///
    /// Currently, the "vicinity" of a subgraph is defined as the set of nodes
    /// that are in the interval between the first and last node of the subgraph
    /// in some topological order. In the worst case this will traverse every
    /// node in the graph and can be improved on in the future.
    pub fn is_node_convex(&self, nodes: impl IntoIterator<Item = G::NodeId>) -> bool {
        // The nodes in the subgraph, in topological order.
        let nodes: BTreeSet<_> = nodes.into_iter().map(|n| self.topsort_ind[n]).collect();
        if nodes.len() <= 1 {
            return true;
        }

        // The range of considered nodes, as positions in the toposorted vector.
        // Since the nodes are ordered, any node outside of this range will
        // necessarily be outside the convex hull.
        let min_ind = *nodes.first().unwrap();
        let max_ind = *nodes.last().unwrap();
        let node_range = min_ind..=max_ind;

        let mut node_iter = nodes.iter().copied().peekable();

        // Nodes in the causal future of `nodes` (inside `node_range`).
        let mut other_nodes = BTreeSet::new();

        loop {
            if node_iter.peek().is_none() {
                break;
            }
            if other_nodes.is_empty() || node_iter.peek() < other_nodes.first() {
                let current = node_iter.next().unwrap();
                let current_node = self.topsort_nodes[current];
                for neighbour in self
                    .graph
                    .neighbors_directed(current_node, petgraph::Direction::Outgoing)
                    .map(|n| self.topsort_ind[n])
                    .filter(|ind| node_range.contains(ind))
                {
                    if !nodes.contains(&neighbour) {
                        other_nodes.insert(neighbour);
                    }
                }
            } else {
                let current = other_nodes.pop_first().unwrap();
                let current_node = self.topsort_nodes[current];
                for neighbour in self
                    .graph
                    .neighbors_directed(current_node, petgraph::Direction::Outgoing)
                    .map(|n| self.topsort_ind[n])
                    .filter(|ind| node_range.contains(ind))
                {
                    if nodes.contains(&neighbour) {
                        // A non-subgraph node in the causal future of the subgraph has an output neighbour in the subgraph.
                        return false;
                    } else {
                        other_nodes.insert(neighbour);
                    }
                }
            }
        }
        true
    }
}
