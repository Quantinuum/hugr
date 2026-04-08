//! Implementations of petgraph's traits for Hugr Region views.
use petgraph::visit as pv;
use portgraph::{LinkView, NodeIndex as NIdx, PortOffset};

/// Wraps some property of an edge that may either be an original edge in the Hugr
/// or a synthetic edge - currently only those added for ordering constraints,
/// but this could be extended in the future.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MaybeSynEdge<T> {
    /// The original data for an original edge in the Hugr
    Original(T),
    /// Edge is synthetic and represents the ordering constraint that the source
    /// node must be ordered before the target because of a nonlocal [EdgeKind::Value]
    /// edge in the original Hugr between the source and a strict descendant of the target.
    NonLocalOrderingConstraint,
}

/// Wrapper for a [LinkView] that implements petgraph traits and adds some extra edges.
#[derive(Clone, Debug)]
pub(super) struct SynEdgeWrapper<T: LinkView> {
    pub(super) region_view: T,
    #[allow(clippy::type_complexity)]
    pub(super) syn_edges: Vec<(NIdx<T::NodeIndexBase>, NIdx<T::NodeIndexBase>)>,
}

impl<T: LinkView> pv::GraphBase for SynEdgeWrapper<T> {
    type NodeId = NIdx<T::NodeIndexBase>;
    type EdgeId = (
        NIdx<T::NodeIndexBase>,
        NIdx<T::NodeIndexBase>,
        MaybeSynEdge<(PortOffset<T::PortOffsetBase>, PortOffset<T::PortOffsetBase>)>,
    );
}

impl<T: LinkView> pv::GraphProp for SynEdgeWrapper<T> {
    type EdgeType = petgraph::Directed;
}

impl<T: LinkView> pv::NodeCount for SynEdgeWrapper<T> {
    fn node_count(&self) -> usize {
        self.region_view.node_count()
    }
}

impl<T: LinkView> pv::NodeIndexable for SynEdgeWrapper<T> {
    fn node_bound(&self) -> usize {
        // ALAN copied from petgraph; but are `NodeIndex`es always dense?
        self.region_view.node_count()
    }

    fn to_index(&self, ix: Self::NodeId) -> usize {
        ix.index()
    }

    fn from_index(&self, ix: usize) -> Self::NodeId {
        NIdx::new(ix)
    }
}

impl<T: LinkView> pv::EdgeCount for SynEdgeWrapper<T> {
    fn edge_count(&self) -> usize {
        self.region_view.link_count() + self.syn_edges.len()
    }
}

impl<T: LinkView> pv::Data for SynEdgeWrapper<T> {
    /// Turns out the underlying [FlatRegion] has unit node weights, we may want to fix that.
    ///
    /// [FlatRegion]: portgraph::view::FlatRegion
    type NodeWeight = ();

    /// Turns out the underlying [FlatRegion] has unit edge weights; we may want to fix that,
    /// but at least this distinguishes synthetic edges from original edges.
    ///
    /// [FlatRegion]: portgraph::view::FlatRegion
    type EdgeWeight = MaybeSynEdge<(PortOffset<T::PortOffsetBase>, PortOffset<T::PortOffsetBase>)>;
}

impl<'a, T: LinkView> pv::IntoNodeReferences for &'a SynEdgeWrapper<T> {
    type NodeRef = NIdx<T::NodeIndexBase>;
    type NodeReferences = Box<dyn Iterator<Item = NIdx<T::NodeIndexBase>> + 'a>;

    fn node_references(self) -> Self::NodeReferences {
        Box::new(self.region_view.nodes_iter())
    }
}

impl<'a, T: LinkView> pv::IntoNodeIdentifiers for &'a SynEdgeWrapper<T> {
    type NodeIdentifiers = Box<dyn Iterator<Item = Self::NodeId> + 'a>;

    fn node_identifiers(self) -> Self::NodeIdentifiers {
        pv::IntoNodeReferences::node_references(self)
    }
}

impl<'a, T: LinkView> pv::IntoNeighbors for &'a SynEdgeWrapper<T> {
    type Neighbors = Box<dyn Iterator<Item = NIdx<T::NodeIndexBase>> + 'a>;

    fn neighbors(self, n: Self::NodeId) -> Self::Neighbors {
        Box::new(
            self.region_view.output_neighbours(n).chain(
                self.syn_edges
                    .iter()
                    .filter_map(move |(src, dst)| (*src == n).then_some(*dst)),
            ),
        )
    }
}

/// An edge in the derived graph - either an original edge, or a synthetic edge.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct EdgeRef<NId, PId> {
    src: NId,
    tgt: NId,
    weight: MaybeSynEdge<(PId, PId)>,
}

impl<NId: Copy, PId: Copy> pv::EdgeRef for EdgeRef<NId, PId> {
    type NodeId = NId;
    type EdgeId = (NId, NId, MaybeSynEdge<(PId, PId)>);
    type Weight = MaybeSynEdge<(PId, PId)>;

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
        (self.src, self.tgt, self.weight)
    }
}

impl<'a, T: LinkView> pv::IntoEdgeReferences for &'a SynEdgeWrapper<T> {
    type EdgeRef = EdgeRef<NIdx<T::NodeIndexBase>, PortOffset<T::PortOffsetBase>>;
    type EdgeReferences = Box<dyn Iterator<Item = Self::EdgeRef> + 'a>;

    fn edge_references(self) -> Self::EdgeReferences {
        Box::new(
            self.region_view
                .nodes_iter()
                .flat_map(|n| {
                    self.region_view
                        .links(n, portgraph::Direction::Outgoing)
                        .map(|(src, tgt)| {
                            let er: Self::EdgeRef = EdgeRef {
                                src: self.region_view.port_node(src).unwrap(),
                                tgt: self.region_view.port_node(tgt).unwrap(),
                                weight: MaybeSynEdge::Original((
                                    self.region_view.port_offset(src).unwrap(),
                                    self.region_view.port_offset(tgt).unwrap(),
                                )),
                            };
                            er
                        })
                })
                .chain(self.syn_edges.iter().map(|(src, tgt)| EdgeRef {
                    src: *src,
                    tgt: *tgt,
                    weight: MaybeSynEdge::NonLocalOrderingConstraint,
                })),
        )
    }
}

impl<'a, T: LinkView> pv::IntoNeighborsDirected for &'a SynEdgeWrapper<T> {
    type NeighborsDirected = Box<dyn Iterator<Item = NIdx<T::NodeIndexBase>> + 'a>;

    fn neighbors_directed(
        self,
        n: Self::NodeId,
        d: petgraph::Direction,
    ) -> Self::NeighborsDirected {
        Box::new(
            self.region_view
                .neighbours(n, d.into())
                .chain(self.syn_edges.iter().filter_map(move |(src, dst)| match d {
                    petgraph::Direction::Outgoing if *src == n => Some(*dst),
                    petgraph::Direction::Incoming if *dst == n => Some(*src),
                    _ => None,
                })),
        )
    }
}

impl<T: LinkView + pv::Visitable<Map: pv::VisitMap<NIdx<T::NodeIndexBase>>>> pv::Visitable
    for SynEdgeWrapper<T>
{
    type Map = T::Map;

    fn visit_map(&self) -> Self::Map {
        self.region_view.visit_map()
    }

    fn reset_map(&self, map: &mut Self::Map) {
        self.region_view.reset_map(map);
    }
}

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

        let sg = simple_dfg_hugr.scheduling_graph(simple_dfg_hugr.module_root());
        let n = pv::NodeFiltered::from_fn(&sg.graph, |n| n.index() % 2 == 0);
        check_into_edges(&sg.graph);
        check_into_edges(&n);
        pv::Topo::new(&sg.graph)
            .iter(&sg.graph)
            .for_each(|n| println!("Node: {:?}", n));
        pv::Topo::new(sg.graph())
            .iter(sg.graph())
            .for_each(|n| println!("Node from graph(): {:?}", n));
    }
}
