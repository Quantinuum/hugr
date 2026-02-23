//! Pass for removing dead code, i.e. that computes values that are then discarded

use hugr_core::hugr::internal::HugrInternals;
use hugr_core::{HugrView, Node, hugr::hugrmut::HugrMut, ops::OpType};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Display, Formatter};
use std::sync::Arc;

use crate::ComposablePass;

/// Configuration for Dead Code Elimination pass
#[derive(Clone)]
pub struct DeadCodeElimPass<H: HugrView> {
    /// Nodes that are definitely needed - e.g. `FuncDefns`, but could be anything.
    /// Hugr Root is assumed to be an entry point even if not mentioned here.
    entry_points: Vec<H::Node>,
    /// Callback identifying nodes that must be preserved even if their
    /// results are not used. Defaults to [`PreserveNode::default_for`].
    preserve_callback: Arc<PreserveCallback<H>>,
}

impl<H: HugrView + 'static> Default for DeadCodeElimPass<H> {
    fn default() -> Self {
        Self {
            entry_points: Default::default(),
            preserve_callback: Arc::new(PreserveNode::default_for),
        }
    }
}

impl<H: HugrView> Debug for DeadCodeElimPass<H> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        // Use "derive Debug" by defining an identical struct without the unprintable fields

        #[allow(unused)] // Rust ignores the derive-Debug in figuring out what's used
        #[derive(Debug)]
        struct DCEDebug<'a, N> {
            entry_points: &'a Vec<N>,
        }

        Debug::fmt(
            &DCEDebug {
                entry_points: &self.entry_points,
            },
            f,
        )
    }
}

/// Callback that identifies nodes that must be preserved even if their
/// results are not used. For example, (the default) [`PreserveNode::default_for`].
pub type PreserveCallback<H> = dyn Fn(&H, <H as HugrInternals>::Node) -> PreserveNode;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// Signal that a node must be preserved even when its result is not used
pub enum PreserveNode {
    /// The node must be kept (nodes inside it may be removed)
    MustKeep,
    /// The node can be removed, even if nodes inside it must be kept
    /// - this will remove the descendants too, so use with care.
    CanRemoveIgnoringChildren,
    /// The node may be removed if-and-only-if all of its children can
    /// (must be kept iff any of its children must be kept).
    DeferToChildren,
}

impl PreserveNode {
    /// A conservative default for a given node. Just examines the node's [`OpType`]:
    /// * Assumes all Calls must be preserved. (One could scan the called `FuncDefn`, but would
    ///   also need to check for cycles in the [`ModuleGraph`](hugr_core::module_graph::ModuleGraph).)
    /// * Assumes all CFGs must be preserved. (One could, for example, allow acyclic
    ///   CFGs to be removed.)
    /// * Assumes all `TailLoops` must be preserved. (One could, for example, use dataflow
    ///   analysis to allow removal of `TailLoops` that never [Continue](hugr_core::ops::TailLoop::CONTINUE_TAG).)
    pub fn default_for<H: HugrView>(h: &H, n: H::Node) -> PreserveNode {
        match h.get_optype(n) {
            OpType::CFG(_) | OpType::TailLoop(_) | OpType::Call(_) => PreserveNode::MustKeep,
            _ => Self::DeferToChildren,
        }
    }
}

/// Errors from [DeadCodeElimPass]
#[derive(Clone, Debug, thiserror::Error, PartialEq)]
#[non_exhaustive]
pub enum DeadCodeElimError<N: Display = Node> {
    /// A node specified to [DeadCodeElimPass::with_entry_points] was not found
    #[error("Node {_0} does not exist in the Hugr")]
    NodeNotFound(N),
}

impl<H: HugrView> DeadCodeElimPass<H> {
    /// Allows setting a callback that determines whether a node must be preserved
    /// (even when its result is not used)
    pub fn set_preserve_callback(mut self, cb: Arc<PreserveCallback<H>>) -> Self {
        self.preserve_callback = cb;
        self
    }

    /// Mark some nodes as entry points to the Hugr, i.e. so we cannot eliminate any code
    /// used to evaluate these nodes.
    /// [`HugrView::entrypoint`] is assumed to be an entry point;
    /// for Module roots the client will want to mark some of the `FuncDefn` children
    /// as entry points too.
    pub fn with_entry_points(mut self, entry_points: impl IntoIterator<Item = H::Node>) -> Self {
        self.entry_points.extend(entry_points);
        self
    }

    fn find_needed_nodes(&self, h: &H) -> Result<HashSet<H::Node>, DeadCodeElimError<H::Node>> {
        let mut must_preserve = HashMap::new();
        let mut needed = HashSet::new();
        let mut q = VecDeque::from_iter(self.entry_points.iter().copied());
        q.push_front(h.entrypoint());
        while let Some(n) = q.pop_front() {
            if !h.contains_node(n) {
                return Err(DeadCodeElimError::NodeNotFound(n));
            }
            if !needed.insert(n) {
                continue;
            }
            for (i, ch) in h.children(n).enumerate() {
                if self.must_preserve(h, &mut must_preserve, ch)
                    || match h.get_optype(ch) {
                        OpType::Case(_)  // Include all Cases in Conditionals
                        | OpType::ExitBlock(_)
                        | OpType::AliasDecl(_) // and all Aliases (we do not track their uses in types)
                        | OpType::AliasDefn(_)
                        | OpType::Input(_) // Also Dataflow input/output, these are necessary for legality
                        | OpType::Output(_) => true,
                        // Assumes entry block is always the first child of a CFG.
                        OpType::DataflowBlock(_) => h.get_optype(n).is_cfg() && i == 0,
                        // Do not include FuncDecl / FuncDefn / Const,
                        // unless reachable by static edges (from Call/LoadConst/LoadFunction)
                        _ => false,
                    }
                {
                    q.push_back(ch);
                }
            }
            if matches!(h.get_optype(n), OpType::DataflowBlock(_) | OpType::ExitBlock(_) ){
                // Follow control flow forwards to find reachable basic blocks besides entry and exit.
                q.extend(h.output_neighbours(n))
            } else {
                // Follow dataflow demand (including e.g edges from Call to FuncDefn) backwards.
                q.extend(h.input_neighbours(n));
            }
            // Also keep consumers of any linear outputs
            if let Some(sig) = h.signature(n) {
                for op in sig.output_ports() {
                    if !sig.out_port_type(op).unwrap().copyable() {
                        q.extend(h.linked_inputs(n, op).map(|(n, _inp)| n))
                    }
                }
            }
        }
        Ok(needed)
    }

    fn must_preserve(&self, h: &H, cache: &mut HashMap<H::Node, bool>, n: H::Node) -> bool {
        if let Some(res) = cache.get(&n) {
            return *res;
        }
        let res = match self.preserve_callback.as_ref()(h, n) {
            PreserveNode::MustKeep => true,
            PreserveNode::CanRemoveIgnoringChildren => false,
            PreserveNode::DeferToChildren => {
                h.children(n).any(|ch| self.must_preserve(h, cache, ch))
            }
        };
        cache.insert(n, res);
        res
    }
}

impl<H: HugrMut> ComposablePass<H> for DeadCodeElimPass<H> {
    type Error = DeadCodeElimError<H::Node>;
    type Result = ();

    fn run(&self, hugr: &mut H) -> Result<(), Self::Error> {
        let needed = self.find_needed_nodes(&*hugr)?;
        let remove = hugr
            .entry_descendants()
            .filter(|n| !needed.contains(n))
            .collect::<Vec<_>>();
        for n in remove {
            hugr.remove_node(n);
        }
        Ok(())
    }
}
#[cfg(test)]
mod test {
    use std::sync::Arc;

    use hugr_core::builder::{
        CFGBuilder, Container, DFGBuilder, Dataflow, DataflowHugr, DataflowSubContainer,
        HugrBuilder, endo_sig, inout_sig,
    };
    use hugr_core::extension::prelude::{ConstUsize, bool_t, qb_t, usize_t};
    use hugr_core::extension::{ExtensionId, Version};
    use hugr_core::ops::{ExtensionOp, OpType};
    use hugr_core::ops::{OpTag, OpTrait, handle::NodeHandle};
    use hugr_core::types::Signature;
    use hugr_core::{Extension, Hugr};
    use hugr_core::{HugrView, ops::Value, type_row};
    use itertools::Itertools;

    use crate::ComposablePass;

    use super::{DeadCodeElimPass, PreserveNode};

    #[test]
    fn test_cfg_callback() {
        let mut cb = CFGBuilder::new(Signature::new_endo(type_row![])).unwrap();
        let cst_unused = cb.add_constant(Value::from(ConstUsize::new(3)));
        let cst_used_in_dfg = cb.add_constant(Value::from(ConstUsize::new(5)));
        let cst_used = cb.add_constant(Value::unary_unit_sum());
        let mut block = cb.entry_builder([type_row![]], type_row![]).unwrap();
        let mut dfg_unused = block
            .dfg_builder(Signature::new(type_row![], usize_t()), [])
            .unwrap();
        let lc_unused = dfg_unused.load_const(&cst_unused);
        let lc1 = dfg_unused.load_const(&cst_used_in_dfg);
        let dfg_unused = dfg_unused.finish_with_outputs([lc1]).unwrap().node();
        let pred = block.load_const(&cst_used);
        let block = block.finish_with_outputs(pred, []).unwrap();
        let exit = cb.exit_block();
        cb.branch(&block, 0, &exit).unwrap();
        let orig = cb.finish_hugr().unwrap();

        // Callbacks that allow removing the DFG (and cst_unused)
        for dce in [
            DeadCodeElimPass::<Hugr>::default(),
            // keep the node inside the DFG, but remove the DFG without checking its children:
            DeadCodeElimPass::default().set_preserve_callback(Arc::new(move |h, n| {
                if n == dfg_unused || h.get_optype(n).is_const() {
                    PreserveNode::CanRemoveIgnoringChildren
                } else {
                    PreserveNode::MustKeep
                }
            })),
        ] {
            let mut h = orig.clone();
            dce.run(&mut h).unwrap();
            assert_eq!(
                h.children(h.entrypoint()).collect_vec(),
                [block.node(), exit.node(), cst_used.node()]
            );
            assert_eq!(
                h.children(block.node())
                    .map(|n| h.get_optype(n).tag())
                    .collect_vec(),
                [OpTag::Input, OpTag::Output, OpTag::LoadConst]
            );
        }

        // Callbacks that prevent removing any node...
        fn keep_if(b: bool) -> PreserveNode {
            if b {
                PreserveNode::MustKeep
            } else {
                PreserveNode::DeferToChildren
            }
        }
        for dce in [
            DeadCodeElimPass::<Hugr>::default()
                .set_preserve_callback(Arc::new(|_, _| PreserveNode::MustKeep)),
            // keeping the unused node in the DFG, means keeping the DFG (which uses its other children)
            DeadCodeElimPass::default()
                .set_preserve_callback(Arc::new(move |_, n| keep_if(n == lc_unused.node()))),
        ] {
            let mut h = orig.clone();
            dce.run(&mut h).unwrap();
            assert_eq!(orig, h);
        }

        // Callbacks that keep the DFG but allow removing the unused constant
        for dce in [
            DeadCodeElimPass::<Hugr>::default()
                .set_preserve_callback(Arc::new(move |_, n| keep_if(n == dfg_unused))),
            DeadCodeElimPass::default()
                .set_preserve_callback(Arc::new(move |_, n| keep_if(n == lc1.node()))),
        ] {
            let mut h = orig.clone();
            dce.run(&mut h).unwrap();
            assert_eq!(
                h.children(h.entrypoint()).collect_vec(),
                [
                    block.node(),
                    exit.node(),
                    cst_used_in_dfg.node(),
                    cst_used.node()
                ]
            );
            assert_eq!(
                h.children(block.node()).skip(2).collect_vec(),
                [dfg_unused, pred.node()]
            );
            assert_eq!(
                h.children(dfg_unused.node())
                    .map(|n| h.get_optype(n).tag())
                    .collect_vec(),
                [OpTag::Input, OpTag::Output, OpTag::LoadConst]
            );
        }

        // Callback that allows removing the DFG but require keeping cst_unused
        {
            let cst_unused = cst_unused.node();
            let mut h = orig.clone();
            DeadCodeElimPass::<Hugr>::default()
                .set_preserve_callback(Arc::new(move |_, n| keep_if(n == cst_unused)))
                .run(&mut h)
                .unwrap();
            assert_eq!(
                h.children(h.entrypoint()).collect_vec(),
                [block.node(), exit.node(), cst_unused, cst_used.node()]
            );
            assert_eq!(
                h.children(block.node())
                    .map(|n| h.get_optype(n).tag())
                    .collect_vec(),
                [OpTag::Input, OpTag::Output, OpTag::LoadConst]
            );
        }
    }

    #[test]
    fn preserve_linear() {
        // A simple linear alloc/measure. Note we do *not* model ordering among allocations for this test.
        let test_ext = Extension::new_arc(
            ExtensionId::new_unchecked("test_qext"),
            Version::new(0, 0, 0),
            |e, w| {
                e.add_op("new".into(), "".into(), inout_sig(vec![], qb_t()), w)
                    .unwrap();
                e.add_op("gate".into(), "".into(), endo_sig(qb_t()), w)
                    .unwrap();
                e.add_op("measure".into(), "".into(), inout_sig(qb_t(), bool_t()), w)
                    .unwrap();
                e.add_op("not".into(), "".into(), endo_sig(bool_t()), w)
                    .unwrap();
            },
        );
        let [new, gate, measure, not] = ["new", "gate", "measure", "not"]
            .map(|n| ExtensionOp::new(test_ext.get_op(n).unwrap().clone(), []).unwrap());
        let mut dfb = DFGBuilder::new(endo_sig(qb_t())).unwrap();
        // Unused new...measure, can be removed
        let qn = dfb.add_dataflow_op(new.clone(), []).unwrap().outputs();
        let [_] = dfb
            .add_dataflow_op(measure.clone(), qn)
            .unwrap()
            .outputs_arr();

        // Free (measure) the input, so not connected to the output
        let [q_in] = dfb.input_wires_arr();
        let [h_in] = dfb
            .add_dataflow_op(gate.clone(), [q_in])
            .unwrap()
            .outputs_arr();
        let [b] = dfb.add_dataflow_op(measure, [h_in]).unwrap().outputs_arr();
        // Operate on the bool only, can be removed as not linear:
        dfb.add_dataflow_op(not, [b]).unwrap();

        // Alloc a new qubit and output that
        let q = dfb.add_dataflow_op(new, []).unwrap().outputs();
        let outs = dfb.add_dataflow_op(gate, q).unwrap().outputs();
        let mut h = dfb.finish_hugr_with_outputs(outs).unwrap();
        DeadCodeElimPass::default().run(&mut h).unwrap();
        // This was failing before https://github.com/CQCL/hugr/pull/2560:
        h.validate().unwrap();

        // Remove one new and measure, and a "not"; keep both gates
        // (cannot remove the other gate or measure even tho results not needed).
        // Removing the gate because the measure-result is not used is beyond (current) DeadCodeElim.
        let ext_ops = h
            .nodes()
            .filter_map(|n| h.get_optype(n).as_extension_op())
            .map(ExtensionOp::unqualified_id);
        assert_eq!(
            ext_ops.sorted().collect_vec(),
            ["gate", "gate", "measure", "new"]
        );
    }

    #[test]
    fn remove_unreachable_bb() {
        let mut cb = CFGBuilder::new(Signature::new_endo(type_row![])).unwrap();

        let cst_unused = cb.add_constant(Value::from(ConstUsize::new(3)));
        let b1_pred = cb.add_constant(Value::unary_unit_sum());
        let b2_pred = cb.add_constant(Value::unit_sum(0, 2).expect("0 < 2"));

        // Entry block
        let mut entry = cb.entry_builder([type_row![]], type_row![]).unwrap();
        let pred1 = entry.load_const(&b1_pred);
        let entry = entry.finish_with_outputs(pred1, []).unwrap();

        // Reachable block
        let mut block_reachable = cb
            .simple_block_builder(Signature::new(type_row![], type_row![]), 1)
            .unwrap();
        let pred2 = block_reachable.load_const(&b1_pred);
        let block_reachable = block_reachable.finish_with_outputs(pred2, []).unwrap();

        // Unreachable block
        let mut block_unreachable = cb
            .simple_block_builder(Signature::new(type_row![], type_row![]), 2)
            .unwrap();
        let _ = block_unreachable.load_const(&cst_unused);
        let pred3 = block_unreachable.load_const(&b2_pred);
        let block_unreachable = block_unreachable.finish_with_outputs(pred3, []).unwrap();

        // Exit block
        let exit = cb.exit_block();

        // Construct CFG
        cb.branch(&entry, 0, &block_reachable).unwrap();
        cb.branch(&block_reachable, 0, &exit).unwrap();
        cb.branch(&block_unreachable, 0, &exit).unwrap();
        // Addtionally add a loop to check it works with a cycle
        cb.branch(&block_unreachable, 1, &block_unreachable)
            .unwrap();
        let mut h = cb.finish_hugr().unwrap();
        h.validate().unwrap();
        let num_nodes_before = h.nodes().count();
        let cfg_node = h.entrypoint();
        let num_cfg_children_before: usize = h.children(cfg_node)
            .filter(|child| matches!(h.get_optype(*child), OpType::DataflowBlock(_)))
            .count();

        // Run pass and check that unreachable block is removed
        DeadCodeElimPass::default().run(&mut h).unwrap();
        h.validate().unwrap();

        // Check we removed the expected number of nodes.
        // 7 nodes removed:
        // - 1 block (block_unreachable)
        // - 2 constants (cst_unused, b2_pred)
        // - 4 ops in the unreachable block (2 LoadConst, the block's Input and Output)
        let num_nodes_after = h.nodes().count();
        assert_eq!(num_nodes_before - num_nodes_after, 7);

        // Check that `block_unreachable` is no longer a valid node.
        assert!(!h.contains_node(block_unreachable.node()));

        // CFG checks: should still be a CFG and have one less dataflow block child.
        assert!(h.get_optype(cfg_node).is_cfg());
        let num_cfg_children_after: usize = h.children(cfg_node)
            .filter(|child| matches!(h.get_optype(*child), OpType::DataflowBlock(_)))
            .count();
        assert_eq!(num_cfg_children_after, num_cfg_children_before - 1);

        // Also the exit block should only have one predecessor now.
        let exit_preds = h.input_neighbours(exit.node()).collect_vec();
        assert_eq!(exit_preds.len(), 1);

    }
}
