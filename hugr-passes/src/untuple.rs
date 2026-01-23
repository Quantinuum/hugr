//! Pass for removing redundant tuple pack->unpack operations.

use std::collections::VecDeque;

use hugr_core::builder::{DFGBuilder, Dataflow, DataflowHugr};
use hugr_core::extension::prelude::{MakeTuple, UnpackTuple};
use hugr_core::hugr::SimpleReplacementError;
use hugr_core::hugr::hugrmut::HugrMut;
use hugr_core::hugr::views::SiblingSubgraph;
use hugr_core::hugr::views::sibling_subgraph::TopoConvexChecker;
use hugr_core::ops::{OpTrait, OpType};
use hugr_core::types::Type;
use hugr_core::{HugrView, Node, SimpleReplacement};
use itertools::{Either, Itertools};

use crate::{ComposablePass, PassScope};

/// Configuration enum for the untuple rewrite pass.
///
/// Indicates whether the pattern match should traverse the HUGR recursively.
#[deprecated(note = "Use PassScope instead")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UntupleRecursive {
    /// Traverse the HUGR recursively, i.e. consider the entire subtree
    Recursive,
    /// Do not traverse the HUGR recursively, i.e. consider only the sibling subgraph
    NonRecursive,
}

#[expect(deprecated)] // Remove along with UntupleRecursive
#[expect(clippy::derivable_impls)] // derive(Default) generates deprecation warning
impl Default for UntupleRecursive {
    fn default() -> Self {
        UntupleRecursive::NonRecursive
    }
}

/// A pass that removes unnecessary `MakeTuple` operations immediately followed
/// by `UnpackTuple`s.
///
/// If the tuple output is consumed by other operations, only the `UnpackTuple`s
/// are removed and their outputs are connected to the original values
/// accordingly.
///
/// Currently only unpack operations in the same region as the `MakeTuple` are
/// removed. This may be extended in the future.
///
/// Removes `MakeTuple` operations that are not consumed by any other
/// operations.
///
/// # Panics
///
/// - Order edges are not supported yet. The pass currently panics if it encounters
///   a pack/unpack pair with connected order edges. See <https://github.com/CQCL/hugr/issues/1974>.
#[derive(Debug, Clone)]
pub struct UntuplePass {
    /// Either a [PassScope] controlling which parts of the Hugr to process;
    /// or a flag for recursiveness, and the parent node under which to operate
    /// (None indicating the Hugr root)
    #[expect(deprecated)] // remove Right half and just use PassScope
    scope: Either<PassScope, (UntupleRecursive, Option<Node>)>,
}

impl Default for UntuplePass {
    fn default() -> Self {
        // TODO Move to PassScope::Default() when UntupleRecursive is removed
        Self {
            scope: Either::Right((Default::default(), Default::default())),
        }
    }
}

#[expect(deprecated)] // Remove along with UntupleRecursive
impl From<UntupleRecursive> for bool {
    fn from(value: UntupleRecursive) -> Self {
        value == UntupleRecursive::Recursive
    }
}

#[derive(Debug, derive_more::Display, derive_more::Error, derive_more::From)]
#[non_exhaustive]
/// Errors produced by [`UntuplePass`].
pub enum UntupleError {
    /// Rewriting the circuit failed.
    RewriteError(SimpleReplacementError),
}

/// Result type for the untuple pass.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct UntupleResult {
    /// Number of `MakeTuple` rewrites applied.
    pub rewrites_applied: usize,
}

impl UntuplePass {
    /// Create a new untuple pass with the given recursiveness and that
    /// will run on the entrypoint region/subtree.
    #[must_use]
    #[deprecated(note = "Use new_scoped or default instead")]
    #[expect(deprecated)] // Remove along with UntupleRecursive
    pub fn new(recursive: UntupleRecursive) -> Self {
        Self {
            scope: Either::Right((recursive, None)),
        }
    }

    /// Create a new untuple pass with the given configuration
    #[must_use]
    pub fn new_scoped(scope: PassScope) -> Self {
        Self {
            scope: Either::Left(scope),
        }
    }

    /// Sets the parent node to optimize (overwrites any previous setting)
    ///
    /// If the pass was previously configured by [Self::with_scope] then
    /// implicitly `[Self::set_recursive]`'s with thee [PassScope::recursive]
    #[deprecated(note = "Use with_scope instead")]
    #[expect(deprecated)] // Remove along with UntupleRecursive
    pub fn set_parent(mut self, parent: impl Into<Option<Node>>) -> Self {
        match &mut self.scope {
            Either::Left(p) => {
                let rec = if p.recursive() {
                    UntupleRecursive::Recursive
                } else {
                    UntupleRecursive::NonRecursive
                };
                self.scope = Either::Right((rec, parent.into()))
            }
            Either::Right((_, p)) => *p = parent.into(),
        };
        self
    }

    /// Sets whether the pass should traverse the HUGR recursively.
    ///
    /// If the pass was last configured via [Self::with_scope], overrides that,
    /// with `set_parent` of default `None`.
    #[must_use]
    #[deprecated(note = "Use with_scope")]
    #[expect(deprecated)] // Remove along with UntupleRecursive
    pub fn recursive(mut self, recursive: UntupleRecursive) -> Self {
        let parent = self.scope.right().and_then(|(_, p)| p);
        self.scope = Either::Right((recursive, parent));
        self
    }

    /// Find tuple pack operations followed by tuple unpack operations
    /// beneath a specified parent and according to this instance's recursiveness
    /// ([Self::recursive] or [Self::with_scope] + [PassScope::recursive])
    /// and generate rewrites to remove them.
    ///
    /// The returned rewrites are guaranteed to be independent of each other.
    ///
    /// Returns an iterator over the rewrites.
    #[deprecated(note = "Use all_rewrites")]
    pub fn find_rewrites<H: HugrView>(
        &self,
        hugr: &H,
        parent: H::Node,
    ) -> Vec<SimpleReplacement<H::Node>> {
        let recursive = match &self.scope {
            Either::Left(scope) => scope.recursive(),
            Either::Right((rec, _)) => (*rec).into(),
        };
        find_rewrites(hugr, parent, recursive)
    }

    /// Find tuple pack operations followed by tuple unpack operations
    /// and generate rewrites to remove them.
    ///
    /// The returned rewrites are guaranteed to be independent of each other.
    ///
    /// Returns an iterator over the rewrites.
    pub fn all_rewrites<H: HugrView<Node = Node>>(
        &self,
        hugr: &H,
    ) -> Vec<SimpleReplacement<H::Node>> {
        let (recursive, parent) = match &self.scope {
            Either::Left(scope) => {
                let Some(root) = scope.root(hugr) else {
                    return vec![];
                };
                (scope.recursive(), root)
            }
            Either::Right((rec, parent)) => ((*rec).into(), parent.unwrap_or(hugr.entrypoint())),
        };
        find_rewrites(hugr, parent, recursive)
    }
}

fn find_rewrites<H: HugrView>(
    hugr: &H,
    parent: H::Node,
    recursive: bool,
) -> Vec<SimpleReplacement<H::Node>> {
    let mut res = Vec::new();
    let mut children_queue = VecDeque::new();
    children_queue.push_back(parent);

    // Required to create SimpleReplacements.
    let mut convex_checker: Option<TopoConvexChecker<H>> = None;

    while let Some(parent) = children_queue.pop_front() {
        for node in hugr.children(parent) {
            let op = hugr.get_optype(node);
            if let Some(rw) = make_rewrite(hugr, &mut convex_checker, node, op) {
                res.push(rw);
            }
            if recursive && op.is_container() {
                children_queue.push_back(node);
            }
        }
    }
    res
}

impl<H: HugrMut<Node = Node>> ComposablePass<H> for UntuplePass {
    type Error = UntupleError;
    type Result = UntupleResult;

    fn run(&self, hugr: &mut H) -> Result<Self::Result, Self::Error> {
        let rewrites = self.all_rewrites(hugr);
        let rewrites_applied = rewrites.len();
        // The rewrites are independent, so we can always apply them all.
        for rewrite in rewrites {
            hugr.apply_patch(rewrite)?;
        }
        Ok(UntupleResult { rewrites_applied })
    }

    /// Overrides any [Self::set_parent] or [Self::recursive]
    fn with_scope(mut self, scope: &crate::PassScope) -> Self {
        self.scope = Either::Left(scope.clone());
        self
    }
}

/// Returns true if the given optype is a `MakeTuple` operation.
///
/// Boilerplate required due to <https://github.com/CQCL/hugr/issues/1496>
fn is_make_tuple(optype: &OpType) -> bool {
    optype.cast::<MakeTuple>().is_some()
}

/// Returns true if the given optype is an `UnpackTuple` operation.
///
/// Boilerplate required due to <https://github.com/CQCL/hugr/issues/1496>
fn is_unpack_tuple(optype: &OpType) -> bool {
    optype.cast::<UnpackTuple>().is_some()
}

/// If this is a `MakeTuple` operation followed by some number of `UnpackTuple` operations
/// on the same region, return a rewrite to remove them.
///
/// Otherwise, return None.
fn make_rewrite<'h, T: HugrView>(
    hugr: &'h T,
    convex_checker: &mut Option<TopoConvexChecker<'h, T>>,
    node: T::Node,
    op: &OpType,
) -> Option<SimpleReplacement<T::Node>> {
    // Only process MakeTuple operations
    if !is_make_tuple(op) {
        return None;
    }
    let tuple_types = op.dataflow_signature().unwrap().input_types().to_vec();
    let node_parent = hugr.get_parent(node);

    // See if it is followed by a tuple unpack
    let links = hugr
        .linked_inputs(node, 0)
        .map(|(neigh, _)| neigh)
        .collect_vec();

    let unpack_nodes = links
        .iter()
        .filter(|&&neigh| hugr.get_parent(neigh) == node_parent)
        .filter(|&&neigh| is_unpack_tuple(hugr.get_optype(neigh)))
        .copied()
        .collect_vec();

    // If there are no unpacks but the tuple is being used, there's nothing to do.
    if unpack_nodes.is_empty() && !links.is_empty() {
        return None;
    }

    // Remove all unpack operations, and remove the pack operation if all neighbours are unpacks.
    let num_other_outputs = links.len() - unpack_nodes.len();
    Some(remove_pack_unpack(
        hugr,
        convex_checker,
        &tuple_types,
        node,
        unpack_nodes,
        num_other_outputs,
    ))
}

/// Returns a rewrite to remove a tuple pack operation that's followed by unpack operations,
/// and `other_tuple_links` other operations.
fn remove_pack_unpack<'h, T: HugrView>(
    hugr: &'h T,
    convex_checker: &mut Option<TopoConvexChecker<'h, T>>,
    tuple_types: &[Type],
    pack_node: T::Node,
    unpack_nodes: Vec<T::Node>,
    num_other_outputs: usize,
) -> SimpleReplacement<T::Node> {
    let num_unpack_outputs = tuple_types.len() * unpack_nodes.len();

    let parent = hugr.get_parent(pack_node).expect("pack_node has no parent");
    let checker = convex_checker.get_or_insert_with(|| TopoConvexChecker::new(hugr, parent));

    let mut nodes = unpack_nodes;
    nodes.push(pack_node);
    let subcirc = SiblingSubgraph::try_from_nodes_with_checker(nodes, hugr, checker).unwrap();
    let subcirc_signature = subcirc.signature(hugr);

    // The output port order in `SiblingSubgraph::try_from_nodes` is not too well defined.
    // Check that the outputs are in the expected order.
    debug_assert!(
        itertools::equal(
            subcirc_signature.output().iter(),
            tuple_types
                .iter()
                .cycle()
                .take(num_unpack_outputs)
                .chain(itertools::repeat_n(
                    &Type::new_tuple(tuple_types.to_vec()),
                    num_other_outputs
                ))
        ),
        "Unpacked tuple values must come before tupled values"
    );

    let mut replacement = DFGBuilder::new(subcirc_signature).unwrap();
    let mut outputs = Vec::with_capacity(num_unpack_outputs + num_other_outputs);

    // Wire the inputs directly to the unpack outputs
    outputs.extend(replacement.input_wires().cycle().take(num_unpack_outputs));

    // If needed, re-add the tuple pack node and connect its output to the tuple outputs.
    if num_other_outputs > 0 {
        let op = MakeTuple::new(tuple_types.to_vec().into());
        let [tuple] = replacement
            .add_dataflow_op(op, replacement.input_wires())
            .unwrap()
            .outputs_arr();
        outputs.extend(std::iter::repeat_n(tuple, num_other_outputs));
    }

    // These should never fail, as we are defining the replacement ourselves.
    let replacement = replacement
        .finish_hugr_with_outputs(outputs)
        .unwrap_or_else(|e| {
            panic!("Failed to create replacement for removing tuple pack/unpack operations. {e}")
        });
    subcirc
        .create_simple_replacement(hugr, replacement)
        .unwrap_or_else(|e| {
            panic!("Failed to create rewrite for removing tuple pack/unpack operations. {e}")
        })
}

#[cfg(test)]
mod test {
    use super::*;
    use hugr_core::extension::prelude::{UnpackTuple, bool_t, qb_t};

    use hugr_core::Hugr;
    use hugr_core::ops::handle::NodeHandle;
    use hugr_core::types::Signature;
    use rstest::{fixture, rstest};

    /// A simple pack operation with unused output.
    ///
    /// These can be removed entirely.
    #[fixture]
    fn unused_pack() -> Hugr {
        let mut h = DFGBuilder::new(Signature::new(vec![bool_t(), bool_t()], vec![])).unwrap();
        let mut inps = h.input_wires();
        let b1 = inps.next().unwrap();
        let b2 = inps.next().unwrap();

        let _tuple = h.make_tuple([b1, b2]).unwrap();

        h.finish_hugr_with_outputs([]).unwrap()
    }

    /// A simple pack operation followed by an unpack operation.
    ///
    /// These can be removed entirely.
    #[fixture]
    fn simple_pack_unpack() -> Hugr {
        let mut h = DFGBuilder::new(Signature::new_endo(vec![qb_t(), bool_t()])).unwrap();
        let mut inps = h.input_wires();
        let qb1 = inps.next().unwrap();
        let b2 = inps.next().unwrap();

        let tuple = h.make_tuple([qb1, b2]).unwrap();

        let op = UnpackTuple::new(vec![qb_t(), bool_t()].into());
        let [qb1, b2] = h.add_dataflow_op(op, [tuple]).unwrap().outputs_arr();

        h.finish_hugr_with_outputs([qb1, b2]).unwrap()
    }

    /// A simple pack/unpack pair with order edges between them.
    ///
    /// In the future we should be able to preserve some order edges, but for now
    /// we just remove everything.
    #[fixture]
    fn ordered_pack_unpack() -> Hugr {
        let mut h = DFGBuilder::new(Signature::new_endo(vec![qb_t(), bool_t()])).unwrap();
        let mut inps = h.input_wires();
        let qb1 = inps.next().unwrap();
        let b2 = inps.next().unwrap();

        let tuple = h.make_tuple([qb1, b2]).unwrap();
        h.set_order(&h.input(), &tuple.node());

        let op = UnpackTuple::new(vec![qb_t(), bool_t()].into());
        let untuple = h.add_dataflow_op(op, [tuple]).unwrap();
        let [qb1, b2] = untuple.outputs_arr();
        h.set_order(&tuple.node(), &untuple.node());

        h.set_order(&untuple.node(), &h.output());
        h.finish_hugr_with_outputs([qb1, b2]).unwrap()
    }

    /// A pack operation followed by three unpack operations from the same tuple.
    ///
    /// These can be removed entirely.
    #[fixture]
    fn multi_unpack() -> Hugr {
        let mut h = DFGBuilder::new(Signature::new(
            vec![bool_t(), bool_t()],
            vec![bool_t(), bool_t(), bool_t(), bool_t()],
        ))
        .unwrap();
        let mut inps = h.input_wires();
        let b1 = inps.next().unwrap();
        let b2 = inps.next().unwrap();

        let tuple = h.make_tuple([b1, b2]).unwrap();

        let op = UnpackTuple::new(vec![bool_t(), bool_t()].into());
        let [b1, b2] = h.add_dataflow_op(op, [tuple]).unwrap().outputs_arr();

        let op = UnpackTuple::new(vec![bool_t(), bool_t()].into());
        let [b3, b4] = h.add_dataflow_op(op, [tuple]).unwrap().outputs_arr();

        // The last one's outputs are disconnected.
        // TODO: Adding this causes the test to fail due to a `NonCovex` error.
        //let op = UnpackTuple::new(vec![bool_t(), bool_t()].into());
        //let _ = h.add_dataflow_op(op, [tuple]).unwrap();

        h.finish_hugr_with_outputs([b1, b2, b3, b4]).unwrap()
    }

    /// A pack operation followed by an unpack operation, where the tuple is also returned.
    ///
    /// The unpack operation can be removed, but the pack operation cannot.
    #[fixture]
    fn partial_unpack() -> Hugr {
        let mut h = DFGBuilder::new(Signature::new(
            vec![bool_t(), bool_t()],
            vec![
                bool_t(),
                bool_t(),
                Type::new_tuple(vec![bool_t(), bool_t()]),
            ],
        ))
        .unwrap();
        let mut inps = h.input_wires();
        let b1 = inps.next().unwrap();
        let b2 = inps.next().unwrap();

        let tuple = h.make_tuple([b1, b2]).unwrap();

        let op = UnpackTuple::new(vec![bool_t(), bool_t()].into());
        let [b1, b2] = h.add_dataflow_op(op, [tuple]).unwrap().outputs_arr();

        h.finish_hugr_with_outputs([b1, b2, tuple]).unwrap()
    }

    #[rstest]
    #[case::unused(unused_pack(), 1, 2)]
    #[case::simple(simple_pack_unpack(), 1, 2)]
    #[case::multi(multi_unpack(), 1, 2)]
    #[case::partial(partial_unpack(), 1, 3)]
    // TODO: Remove this once <https://github.com/CQCL/hugr/issues/1974>, and update the `UntuplePass` docs.
    #[should_panic(expected = "UnsupportedEdgeKind(Node(7), Port(Incoming, 2))")]
    #[case::ordered(ordered_pack_unpack(), 1, 2)]
    fn test_pack_unpack(
        #[case] mut hugr: Hugr,
        #[case] expected_rewrites: usize,
        #[case] remaining_nodes: usize,
        #[values(true, false)] use_scope: bool,
    ) {
        let parent = hugr.entrypoint();
        let pass = if use_scope {
            UntuplePass::new_scoped(PassScope::EntrypointFlat)
        } else {
            #[expect(deprecated)] // Remove use_scope==false case along with UntupleRecursive
            UntuplePass::default().set_parent(parent)
        };
        let res = pass.run(&mut hugr).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(res.rewrites_applied, expected_rewrites);
        assert_eq!(hugr.children(parent).count(), remaining_nodes);
    }
}
