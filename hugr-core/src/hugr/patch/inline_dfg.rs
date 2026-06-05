//! A rewrite that inlines a DFG node, moving all children
//! of the DFG except Input+Output into the DFG's parent,
//! and deleting the DFG along with its Input + Output

use itertools::Itertools;

use super::{PatchHugrMut, PatchVerification};
use crate::core::HugrNode;
use crate::hugr::HugrMut;
use crate::ops::handle::{DfgID, NodeHandle};
use crate::{HugrView, IncomingPort, Node, OutgoingPort, PortIndex};

/// Structure identifying an `InlineDFG` rewrite from the spec
pub struct InlineDFG<N = Node>(pub DfgID<N>);

/// Errors from an [`InlineDFG`] rewrite.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum InlineDFGError<N = Node> {
    /// Node to inline was not a DFG. (E.g. node has been overwritten since the `DfgID` originated.)
    #[error("{node} was not a DFG")]
    NotDFG {
        /// The node we tried to inline
        node: N,
    },
    /// The DFG node is the hugr entrypoint
    #[error("Cannot inline the entrypoint node, {node}")]
    CantInlineEntrypoint {
        /// The node we tried to inline
        node: N,
    },
}

impl<N: HugrNode> PatchVerification for InlineDFG<N> {
    type Error = InlineDFGError<N>;

    type Node = N;

    fn verify(&self, h: &impl crate::HugrView<Node = N>) -> Result<(), Self::Error> {
        let n = self.0.node();
        if h.get_optype(n).as_dfg().is_none() {
            return Err(InlineDFGError::NotDFG { node: n });
        }
        if n == h.entrypoint() {
            return Err(InlineDFGError::CantInlineEntrypoint { node: n });
        }
        Ok(())
    }

    fn invalidated_nodes(
        &self,
        _: &impl HugrView<Node = Self::Node>,
    ) -> impl Iterator<Item = Self::Node> {
        [self.0.node()].into_iter()
    }
}

impl<N: HugrNode> PatchHugrMut for InlineDFG<N> {
    /// The removed nodes: the DFG, and its Input and Output children.
    type Outcome = [N; 3];

    const UNCHANGED_ON_FAILURE: bool = true;

    fn apply_hugr_mut(self, h: &mut impl HugrMut<Node = N>) -> Result<Self::Outcome, Self::Error> {
        self.verify(h)?;
        let n = self.0.node();
        let (oth_in, oth_out) = {
            let dfg_ty = h.get_optype(n);
            (
                dfg_ty.other_input_port().unwrap(),
                dfg_ty.other_output_port().unwrap(),
            )
        };

        let parent = h.get_parent(n).unwrap();
        let [input, output] = h.get_io(n).unwrap();
        for ch in h.children(n).skip(2).collect::<Vec<_>>() {
            h.set_parent(ch, parent);
        }

        // DFG Inputs.
        for inp in h.node_inputs(n).collect::<Vec<_>>() {
            let dfg_preds = h.linked_outputs(n, inp).collect::<Vec<_>>();
            assert!(inp == oth_in || dfg_preds.len() == 1); // Any number of order preds
            h.disconnect(n, inp); // These disconnects allow permutations to work trivially.
            let outp = OutgoingPort::from(inp.index());
            let mut targets = h.linked_inputs(input, outp).collect::<Vec<_>>();
            h.disconnect(input, outp);
            if inp == oth_in {
                // In order to ensure that any nodes A, B with Order edges A->DFG->B are still ordered
                // after inlining, connect all such pairs A and B directly. This is not strictly necessary
                // in all cases (specifically if there are Order paths from the DFG's Input to Output),
                // but the redundant edges shouldn't cause any issues and can potentially be removed by
                // a later pass.
                targets.extend(h.linked_inputs(n, oth_out));
            }

            for ((src_n, src_p), (tgt_n, tgt_p)) in dfg_preds.into_iter().cartesian_product(targets)
            {
                h.connect(src_n, src_p, tgt_n, tgt_p);
            }
        }
        // DFG Outputs.
        for outport in h.node_outputs(n).collect::<Vec<_>>() {
            let inpp = IncomingPort::from(outport.index());
            let sources = h.linked_outputs(output, inpp).collect::<Vec<_>>();
            assert!(outport == oth_out || sources.len() == 1); // Any number of order sources
            h.disconnect(output, inpp);

            let dfg_succs = h.linked_inputs(n, outport).collect::<Vec<_>>();
            h.disconnect(n, outport);
            for ((src_n, src_p), (tgt_n, tgt_p)) in sources.into_iter().cartesian_product(dfg_succs)
            {
                h.connect(src_n, src_p, tgt_n, tgt_p);
            }
        }
        h.remove_node(input);
        h.remove_node(output);
        assert!(h.children(n).next().is_none());
        h.remove_node(n);
        Ok([n, input, output])
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;
    use std::iter::once;

    use rstest::rstest;

    use crate::builder::{
        Container, DFGBuilder, Dataflow, DataflowHugr, DataflowSubContainer, SubContainer,
        endo_sig, inout_sig,
    };
    use crate::extension::prelude::qb_t;
    use crate::hugr::HugrMut;
    use crate::ops::handle::{DfgID, NodeHandle};
    use crate::ops::{OpType, Value};
    use crate::std_extensions::arithmetic::float_types::{self, float64_type};
    use crate::std_extensions::arithmetic::int_ops::IntOpDef;
    use crate::std_extensions::arithmetic::int_types::{self, ConstInt};
    use crate::types::Signature;
    use crate::utils::test_quantum_extension;
    use crate::{Direction, Hugr, HugrView, Port, Wire, type_row};

    use super::InlineDFG;

    fn find_dfgs<H: HugrView>(h: &H) -> Vec<H::Node> {
        h.entry_descendants()
            .filter(|n| h.get_optype(*n).as_dfg().is_some())
            .collect()
    }
    fn extension_ops<H: HugrView>(h: &H) -> Vec<H::Node> {
        h.nodes()
            .filter(|n| matches!(h.get_optype(*n), OpType::ExtensionOp(_)))
            .collect()
    }

    #[rstest]
    #[case(true)]
    #[case(false)]
    fn inline_add_load_const(#[case] nonlocal: bool) -> Result<(), Box<dyn std::error::Error>> {
        use crate::hugr::patch::inline_dfg::InlineDFGError;

        let int_ty = &int_types::INT_TYPES[6];

        let mut outer = DFGBuilder::new(inout_sig(vec![int_ty.clone(); 2], vec![int_ty.clone()]))?;
        let [a, b] = outer.input_wires_arr();
        fn make_const<T: AsMut<Hugr> + AsRef<Hugr>>(
            d: &mut DFGBuilder<T>,
        ) -> Result<Wire, Box<dyn std::error::Error>> {
            let cst = Value::extension(ConstInt::new_u(6, 15)?);
            let c1 = d.add_load_const(cst);

            Ok(c1)
        }
        let c1 = nonlocal.then(|| make_const(&mut outer));
        let inner = {
            let mut inner = outer.dfg_builder_endo([(int_ty.clone(), a)])?;
            let [a] = inner.input_wires_arr();
            let c1 = c1.unwrap_or_else(|| make_const(&mut inner))?;
            let a1 = inner.add_dataflow_op(IntOpDef::iadd.with_log_width(6), [a, c1])?;
            inner.finish_with_outputs(a1.outputs())?
        };
        let [a1] = inner.outputs_arr();

        let a1_sub_b = outer.add_dataflow_op(IntOpDef::isub.with_log_width(6), [a1, b])?;
        let mut outer = outer.finish_hugr_with_outputs(a1_sub_b.outputs())?;

        // Sanity checks
        assert_eq!(
            outer.children(inner.node()).count(),
            if nonlocal { 3 } else { 5 }
        ); // Input, Output, add; + const, load_const
        assert_eq!(find_dfgs(&outer), vec![outer.entrypoint(), inner.node()]);
        let [add, sub] = extension_ops(&outer).try_into().unwrap();
        assert_eq!(
            outer.get_parent(outer.get_parent(add).unwrap()),
            outer.get_parent(sub)
        );
        assert_eq!(outer.entry_descendants().count(), 10); // 6 above + inner DFG + outer (DFG + Input + Output + sub)
        {
            // Check we can't inline the outer DFG
            let mut h = outer.clone();
            assert_eq!(
                h.apply_patch(InlineDFG(DfgID::from(h.entrypoint()))),
                Err(InlineDFGError::CantInlineEntrypoint {
                    node: h.entrypoint()
                })
            );
            assert_eq!(h, outer); // unchanged
        }

        outer.apply_patch(InlineDFG(*inner.handle()))?;
        outer.validate()?;
        assert_eq!(outer.entry_descendants().count(), 7);
        assert_eq!(find_dfgs(&outer), vec![outer.entrypoint()]);
        let [add, sub] = extension_ops(&outer).try_into().unwrap();
        assert_eq!(outer.get_parent(add), Some(outer.entrypoint()));
        assert_eq!(outer.get_parent(sub), Some(outer.entrypoint()));
        assert_eq!(
            outer.node_connections(add, sub).collect::<Vec<_>>().len(),
            1
        );
        Ok(())
    }

    #[test]
    fn permutation() -> Result<(), Box<dyn std::error::Error>> {
        let mut h = DFGBuilder::new(endo_sig(vec![qb_t(), qb_t()]))?;
        let [p, q] = h.input_wires_arr();
        let [p_h] = h
            .add_dataflow_op(test_quantum_extension::h_gate(), [p])?
            .outputs_arr();
        let swap = {
            let swap = h.dfg_builder(Signature::new_endo([qb_t(), qb_t()]), [p_h, q])?;
            let [a, b] = swap.input_wires_arr();
            swap.finish_with_outputs([b, a])?
        };
        let [q, p] = swap.outputs_arr();
        let cx = h.add_dataflow_op(test_quantum_extension::cx_gate(), [q, p])?;

        let mut h = h.finish_hugr_with_outputs(cx.outputs())?;
        assert_eq!(find_dfgs(&h), vec![h.entrypoint(), swap.node()]);
        assert_eq!(h.entry_descendants().count(), 8); // Dfg+I+O, H, CX, Dfg+I+O
        // No permutation outside the swap DFG:
        assert_eq!(
            h.node_connections(p_h.node(), swap.node())
                .collect::<Vec<_>>(),
            vec![[
                Port::new(Direction::Outgoing, 0),
                Port::new(Direction::Incoming, 0)
            ]]
        );
        assert_eq!(
            h.node_connections(swap.node(), cx.node())
                .collect::<Vec<_>>(),
            vec![
                [
                    Port::new(Direction::Outgoing, 0),
                    Port::new(Direction::Incoming, 0)
                ],
                [
                    Port::new(Direction::Outgoing, 1),
                    Port::new(Direction::Incoming, 1)
                ]
            ]
        );

        h.apply_patch(InlineDFG(*swap.handle()))?;
        assert_eq!(find_dfgs(&h), vec![h.entrypoint()]);
        assert_eq!(h.entry_descendants().count(), 5); // Dfg+I+O
        let mut ops = extension_ops(&h);
        ops.sort_by_key(|n| h.num_outputs(*n)); // Put H before CX
        let [h_gate, cx] = ops.try_into().unwrap();
        // Now permutation exists:
        assert_eq!(
            h.node_connections(h_gate, cx).collect::<Vec<_>>(),
            vec![[
                Port::new(Direction::Outgoing, 0),
                Port::new(Direction::Incoming, 1)
            ]]
        );
        Ok(())
    }

    #[rstest]
    fn order_edges(
        #[values(false, true)] o1: bool,
        #[values(false, true)] o2: bool,
        #[values(false, true)] o3: bool,
        #[values(false, true)] o4: bool,
    ) -> Result<(), Box<dyn std::error::Error>> {
        /*      -----|-----|-----
         *           |     |
         *          H_a   H_b
         *           |.   |?         NB. Order edge H_a to nested DFG
         *           | .  |?         NB. Optional(o1) Order edge from H_b to nested DFG
         *           |  /-|--------\
         *           |  | |? . Cst | NB. Order edge Input to LCst
         *           |  | |? . |   | NB. Optional(o2) Order edge from Input to RZ
         *           |  | |?  LCst |
         *           |  | \? /     |
         *           |  |  RZ      |
         *           |  |  |       |
         *           |  |  meas    |
         *           |  |  |? \    |
         *           |  |  |? if   | NB. Optional(o3) Order edge from meas to Output
         *           |  |  |? .    | NB. Order edge if to Output
         *           |  \--|-------/
         *           |  . ?|         NB. Optional(o4) Order edge from nested DFG to CX
         *           | .  ?|         NB. Order edge nested DFG to H_a2
         *           H_a2 ?|
         *              \ ?/
         *               CX
         */
        let mut outer = DFGBuilder::new(endo_sig(vec![qb_t(), qb_t()]))?;
        let [a, b] = outer.input_wires_arr();
        let h_a = outer.add_dataflow_op(test_quantum_extension::h_gate(), [a])?;
        let h_b = outer.add_dataflow_op(test_quantum_extension::h_gate(), [b])?;
        let mut inner = outer.dfg_builder(endo_sig([qb_t()]), h_b.outputs())?;
        let [i] = inner.input_wires_arr();
        let f = inner.add_load_value(float_types::ConstF64::new(1.0));
        inner.add_other_wire(inner.input().node(), f.node());
        let r = inner.add_dataflow_op(test_quantum_extension::rz_f64(), [i, f])?;
        if o2 {
            inner.add_other_wire(inner.input().node(), r.node());
        }
        let [m, b] = inner
            .add_dataflow_op(test_quantum_extension::measure(), r.outputs())?
            .outputs_arr();
        // Node using the boolean. Here we just select between two empty computations.
        let mut if_n =
            inner.conditional_builder(([type_row![], type_row![]], b), [], type_row![])?;
        if_n.case_builder(0)?.finish_with_outputs([])?;
        if_n.case_builder(1)?.finish_with_outputs([])?;
        let if_n = if_n.finish_sub_container()?;
        inner.add_other_wire(if_n.node(), inner.output().node());
        if o3 {
            inner.add_other_wire(m.node(), inner.output().node());
        }
        let inner = inner.finish_with_outputs([m])?;
        outer.add_other_wire(h_a.node(), inner.node());
        if o1 {
            outer.add_other_wire(h_b.node(), inner.node());
        }
        let h_a2 = outer.add_dataflow_op(test_quantum_extension::h_gate(), h_a.outputs())?;
        outer.add_other_wire(inner.node(), h_a2.node());
        let cx = outer.add_dataflow_op(
            test_quantum_extension::cx_gate(),
            h_a2.outputs().chain(inner.outputs()),
        )?;
        if o4 {
            outer.add_other_wire(inner.node(), cx.node());
        }
        let mut outer = outer.finish_hugr_with_outputs(cx.outputs())?;

        outer.apply_patch(InlineDFG(*inner.handle()))?;
        outer.validate()?;
        let order_neighbours = |n, d| {
            let p = outer.get_optype(n).other_port(d).unwrap();
            outer
                .linked_ports(n, p)
                .map(|(n, _)| n)
                .collect::<HashSet<_>>()
        };
        let ext_order_preds = HashSet::from_iter(once(h_a.node()).chain(o1.then_some(h_b.node())));
        let inp_order_succs = once(f.node()).chain(o2.then_some(r.node()));

        let out_order_preds = once(if_n.node()).chain(o3.then_some(m.node()));
        let ext_order_succs = HashSet::from_iter(once(h_a2.node()).chain(o4.then_some(cx.node())));

        // Order predecessors of DFG get edges to both Input any-successor and DFG Order-successors
        let ext_order_tgts =
            HashSet::from_iter(inp_order_succs.chain(ext_order_succs.iter().cloned()));
        assert_eq!(
            order_neighbours(h_a.node(), Direction::Outgoing),
            ext_order_tgts
        );
        assert_eq!(
            order_neighbours(h_b.node(), Direction::Outgoing),
            if o1 { ext_order_tgts } else { HashSet::new() }
        );
        assert_eq!(
            order_neighbours(f.node(), Direction::Incoming),
            ext_order_preds
        );
        assert_eq!(
            order_neighbours(r.node(), Direction::Incoming),
            if o2 {
                ext_order_preds.clone()
            } else {
                HashSet::new()
            }
        );

        assert_eq!(
            order_neighbours(if_n.node(), Direction::Outgoing),
            ext_order_succs
        );
        assert_eq!(
            order_neighbours(m.node(), Direction::Outgoing),
            if o3 { ext_order_succs } else { HashSet::new() }
        );
        // Order successors of DFG get edges from both Output any-predecessors and DFG Order-predecessors
        let ext_order_srcs = HashSet::from_iter(out_order_preds.chain(ext_order_preds));
        assert_eq!(
            order_neighbours(h_a2.node(), Direction::Incoming),
            ext_order_srcs
        );
        assert_eq!(
            order_neighbours(cx.node(), Direction::Incoming),
            if o4 { ext_order_srcs } else { HashSet::new() }
        );
        Ok(())
    }

    /// Determines whether there is a path along [Order] edges only from `src` to `tgt`.
    ///
    /// [Order]: crate::types::EdgeKind::StateOrder
    fn check_order_reachable<H: HugrView>(h: &H, src: H::Node, tgt: H::Node) {
        let mut visited = HashSet::new();
        let mut to_visit = vec![src];
        while let Some(n) = to_visit.pop() {
            if visited.insert(n) {
                if n == tgt {
                    return;
                }
                let order_outport = h.get_optype(n).other_output_port().unwrap();
                to_visit.extend(h.linked_inputs(n, order_outport).map(|(n, _)| n));
            }
        }
        panic!("Node {tgt:?} not reachable from {src:?}");
    }

    #[test]
    fn order_edge_chain_broken() {
        let mut h = DFGBuilder::new(endo_sig(vec![qb_t()])).unwrap();
        let [q1] = h.input_wires_arr();
        let qfree = h
            .add_dataflow_op(test_quantum_extension::q_discard(), [q1])
            .unwrap();
        assert_eq!(qfree.num_value_outputs(), 0);
        let mut inner = h.dfg_builder(inout_sig([], [float64_type()]), []).unwrap();
        let f = inner.add_load_value(float_types::ConstF64::new(1.0));
        let inner = inner.finish_with_outputs([f]).unwrap();
        let [f] = inner.outputs_arr();
        let qalloc = h
            .add_dataflow_op(test_quantum_extension::q_alloc(), [])
            .unwrap();
        let [q2] = qalloc.outputs_arr();
        let [q2] = h
            .add_dataflow_op(test_quantum_extension::rz_f64(), [q2, f])
            .unwrap()
            .outputs_arr();

        h.add_other_wire(qfree.node(), inner.node());
        h.add_other_wire(inner.node(), qalloc.node());
        let mut h = h.finish_hugr_with_outputs([q2]).unwrap();
        check_order_reachable(&h, qfree.node(), qalloc.node());

        h.apply_patch(InlineDFG(*inner.handle())).unwrap();
        h.validate().unwrap();
        // This was failing prior to https://github.com/Quantinuum/hugr/pull/3072
        check_order_reachable(&h, qfree.node(), qalloc.node());
    }
}
