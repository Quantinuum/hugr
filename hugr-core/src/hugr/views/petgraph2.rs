//! Implementations of petgraph's traits for Hugr Region views.
use petgraph::visit as pv;
use portgraph::NodeIndex as NIdx;
use pv::EdgeRef as _;

/// Wraps some property of an edge that may either be an original edge in the Hugr
/// or a synthetic edge - currently only those added for ordering constraints, but this could be extended in the future.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
// ALAN perhaps should be "MaybeSynEdge"?
pub enum MaybeSynthetic<T> {
    /// The original data for an original edge in the Hugr
    Original(T),
    /// Edge is synthetic and represents the ordering constraint that the source
    /// node must be ordered before the target because of a nonlocal [EdgeKind::Value]
    /// edge in the original Hugr between the source and a strict descendant of the target.
    NonLocalOrderingConstraint,
}

/// Wrapper for a petgraph that adds some extra edges.
#[derive(Clone, Debug)]
pub struct SynEdgeWrapper<T> {
    pub(super) region_view: T,
    pub(super) syn_edges: Vec<(NIdx, NIdx)>,
}

impl<T: pv::GraphBase> pv::GraphBase for SynEdgeWrapper<T> {
    type NodeId = T::NodeId;
    type EdgeId = MaybeSynthetic<T::EdgeId>;
}

impl<T: pv::GraphBase> pv::GraphProp for SynEdgeWrapper<T> {
    type EdgeType = petgraph::Directed;
}

impl<T: pv::GraphBase + pv::NodeCount> pv::NodeCount for SynEdgeWrapper<T> {
    fn node_count(&self) -> usize {
        self.region_view.node_count()
    }
}

impl<T: pv::GraphBase + pv::NodeIndexable> pv::NodeIndexable for SynEdgeWrapper<T> {
    fn node_bound(&self) -> usize {
        self.region_view.node_bound()
    }

    fn to_index(&self, ix: Self::NodeId) -> usize {
        self.region_view.to_index(ix)
    }

    fn from_index(&self, ix: usize) -> Self::NodeId {
        self.region_view.from_index(ix)
    }
}

impl<T: pv::GraphBase + pv::EdgeCount> pv::EdgeCount for SynEdgeWrapper<T> {
    fn edge_count(&self) -> usize {
        self.region_view.edge_count() + self.syn_edges.len()
    }
}

impl<T: pv::GraphBase + pv::Data> pv::Data for SynEdgeWrapper<T> {
    /// Turns out the underlying [FlatRegion] has unit node weights, we may want to fix that.
    ///
    /// [FlatRegion]: portgraph::view::FlatRegion
    type NodeWeight = T::NodeWeight;

    /// Turns out the underlying [FlatRegion] has unit node weights; we may want to fix that,
    /// but at least this distinguishes synthetic edges from original edges.
    ///
    /// [FlatRegion]: portgraph::view::FlatRegion
    type EdgeWeight = MaybeSynthetic<T::EdgeWeight>;
}

impl<T: pv::GraphBase + pv::IntoNodeReferences> pv::IntoNodeReferences for &SynEdgeWrapper<T> {
    type NodeRef = T::NodeRef;
    type NodeReferences = T::NodeReferences;

    fn node_references(self) -> Self::NodeReferences {
        self.region_view.node_references()
    }
}

impl<'a, T: pv::GraphBase> pv::IntoNodeIdentifiers for &'a SynEdgeWrapper<T>
where
    &'a T: pv::IntoNodeIdentifiers<NodeId = T::NodeId>,
{
    type NodeIdentifiers = <&'a T as pv::IntoNodeIdentifiers>::NodeIdentifiers;

    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.region_view.node_identifiers()
    }
}

impl<'a, T> pv::IntoNeighbors for &'a SynEdgeWrapper<T>
where
    T: pv::GraphBase<NodeId = NIdx>,
    &'a T: pv::IntoNeighbors<NodeId = NIdx, Neighbors: 'a>,
{
    type Neighbors = Box<dyn Iterator<Item = NIdx> + 'a>;

    fn neighbors(self, n: Self::NodeId) -> Self::Neighbors {
        Box::new(
            self.region_view.neighbors(n).chain(
                self.syn_edges
                    .iter()
                    .filter_map(move |(src, dst)| (*src == n).then_some(*dst)),
            ),
        )
    }
}

/// An edge in the derived graph - either an original edge, or a synthetic edge.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct EdgeRef<W, ID> {
    src: NIdx,
    tgt: NIdx,
    //Either both will be original, or both synthetic,
    // but since we have to return a reference from `fn weight()` we cannot store together.`
    weight: MaybeSynthetic<W>,
    id: MaybeSynthetic<ID>,
}

impl<W: Copy, ID: Copy> pv::EdgeRef for EdgeRef<W, ID> {
    type NodeId = NIdx;
    type EdgeId = MaybeSynthetic<ID>;
    type Weight = MaybeSynthetic<W>;

    fn source(&self) -> Self::NodeId {
        self.src
    }

    fn target(&self) -> Self::NodeId {
        self.tgt
    }

    fn weight(&self) -> &Self::Weight {
        &self.weight
    }

    fn id(&self) -> Self::EdgeId {
        self.id
    }
}

impl<'a, T, W: Copy> pv::IntoEdgeReferences for &'a SynEdgeWrapper<T>
where
    T: pv::GraphBase<NodeId = NIdx> + pv::Data<EdgeWeight = W>,
    &'a T: pv::IntoEdgeReferences<
            EdgeRef: pv::EdgeRef<NodeId = NIdx, Weight = W, EdgeId = T::EdgeId> + 'a,
        >,
{
    type EdgeRef = EdgeRef<W, T::EdgeId>;
    type EdgeReferences = Box<dyn Iterator<Item = Self::EdgeRef> + 'a>;

    fn edge_references(self) -> Self::EdgeReferences {
        Box::new(
            self.region_view
                .edge_references()
                .map(|er| EdgeRef {
                    src: er.source(),
                    tgt: er.target(),
                    id: MaybeSynthetic::Original(er.id()),
                    weight: MaybeSynthetic::Original(*er.weight()),
                })
                .chain(self.syn_edges.iter().map(|(src, tgt)| EdgeRef {
                    src: *src,
                    tgt: *tgt,
                    id: MaybeSynthetic::NonLocalOrderingConstraint,
                    weight: MaybeSynthetic::NonLocalOrderingConstraint,
                })),
        )
    }
}

impl<'a, T> pv::IntoNeighborsDirected for &'a SynEdgeWrapper<T>
where
    T: pv::GraphBase<NodeId = NIdx>,
    &'a T: pv::IntoNeighborsDirected<NodeId = NIdx, NeighborsDirected: 'a>,
{
    type NeighborsDirected = Box<dyn Iterator<Item = NIdx> + 'a>;

    fn neighbors_directed(
        self,
        n: Self::NodeId,
        d: petgraph::Direction,
    ) -> Self::NeighborsDirected {
        Box::new(
            self.region_view
                .neighbors_directed(n, d)
                .chain(self.syn_edges.iter().filter_map(move |(src, dst)| match d {
                    petgraph::Direction::Outgoing if *src == n => Some(*dst),
                    petgraph::Direction::Incoming if *dst == n => Some(*src),
                    _ => None,
                })),
        )
    }
}

impl<T: pv::GraphBase + pv::Visitable> pv::Visitable for SynEdgeWrapper<T> {
    type Map = T::Map;

    fn visit_map(&self) -> Self::Map {
        self.region_view.visit_map()
    }

    fn reset_map(&self, map: &mut Self::Map) {
        self.region_view.reset_map(map);
    }
}

/*impl <T> pv::GetAdjacencyMatrix for PetgraphWrapper<'_, T>
where
    T: HugrView,
{
    type AdjMatrix = std::collections::HashSet<(Self::NodeId, Self::NodeId)>;

    fn adjacency_matrix(&self) -> Self::AdjMatrix {
        let mut matrix = std::collections::HashSet::new();
        for node in self.hugr.nodes() {
            for neighbour in self.hugr.output_neighbours(node) {
                matrix.insert((node, neighbour));
            }
        }
        matrix
    }

    fn is_adjacent(&self, matrix: &Self::AdjMatrix, a: Self::NodeId, b: Self::NodeId) -> bool {
        matrix.contains(&(a, b))
    }
}*/

#[cfg(test)]
mod test {
    use petgraph::visit as pv;
    use petgraph::visit::Walker as _;
    use rstest::rstest;

    use crate::builder::test::simple_dfg_hugr;
    use crate::{Hugr, HugrView};

    #[rstest]
    fn test(simple_dfg_hugr: Hugr) {
        fn check_into_edges(_x: impl pv::IntoEdgeReferences) {}

        let (region, _node_map) = simple_dfg_hugr.order_graph(simple_dfg_hugr.module_root());
        let n = pv::NodeFiltered::from_fn(&region, |n| n.index() % 2 == 0);
        check_into_edges(&region);
        check_into_edges(&n);
        pv::Topo::new(&region)
            .iter(&region)
            .for_each(|n| println!("Node: {:?}", n));
    }
}
