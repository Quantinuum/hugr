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

        // Order edges. Any paths A -> DFG -> B, where both edges are Order edges,
        // must be preserved as A -> B. (These new edges may be redundant if there
        // are paths through the nodes *inside* the DFG, but that's fine.)

        for ((src_n, src_p), (tgt_n, tgt_p)) in h
            .linked_outputs(n, oth_in)
            .collect::<Vec<_>>()
            .into_iter()
            .cartesian_product(&h.linked_inputs(n, oth_out).collect::<Vec<_>>())
        {
            h.connect(src_n, src_p, *tgt_n, *tgt_p);
        }

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
            let targets = h.linked_inputs(input, outp).collect::<Vec<_>>();
            h.disconnect(input, outp);

            for ((src_n, src_p), (tgt_n, tgt_p)) in
                dfg_preds.into_iter().cartesian_product(&targets)
            {
                h.connect(src_n, src_p, *tgt_n, *tgt_p);
            }
        }
        // DFG Outputs.
        for outport in h.node_outputs(n).collect::<Vec<_>>() {
            let inpp = IncomingPort::from(outport.index());
            let sources = h.linked_outputs(output, inpp).collect::<Vec<_>>();
            assert!(outport == oth_out || sources.len() == 1); // Any number of order sources
            h.disconnect(output, inpp);

            let targets = h.linked_inputs(n, outport).collect::<Vec<_>>();
            h.disconnect(n, outport);
            for ((src_n, src_p), (tgt_n, tgt_p)) in sources.into_iter().cartesian_product(&targets)
            {
                h.connect(src_n, src_p, *tgt_n, *tgt_p);
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
    use crate::std_extensions::arithmetic::float_types;
    use crate::std_extensions::arithmetic::int_ops::IntOpDef;
    use crate::std_extensions::arithmetic::int_types::{self, ConstInt};
    use crate::types::Signature;
    use crate::utils::test_quantum_extension;
    use crate::{Direction, HugrView, Port, type_row};
    use crate::{Hugr, Wire};

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
         *           |  | |?.  Cst | NB. Order edge Input to LCst
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
        // h_a, and optionally h_b, should have Order edges to the F64 load_const,
        // optionally the Rz, also the Order-successors of the DFG
        let input_ord_srcs = HashSet::from_iter(once(h_a.node()).chain(o1.then_some(h_b.node())));
        let input_ord_tgts = HashSet::from_iter(once(f.node()).chain(o2.then_some(r.node())));

        // h_a2, and optionally the CX, should have Order edges from the if,
        // optionally meas, and the Order-predecessors of the DFG
        let output_ord_tgts = HashSet::from_iter(once(h_a2.node()).chain(o4.then_some(cx.node())));
        let output_ord_srcs = HashSet::from_iter(once(if_n.node()).chain(o3.then_some(m.node())));

        for input_ord_src in &input_ord_srcs {
            assert_eq!(
                order_neighbours(*input_ord_src, Direction::Outgoing),
                HashSet::from_iter(input_ord_tgts.union(&output_ord_tgts).copied())
            );
        }
        for input_ord_tgt in &input_ord_tgts {
            assert_eq!(
                order_neighbours(*input_ord_tgt, Direction::Incoming),
                input_ord_srcs
            );
        }
        for output_ord_src in &output_ord_srcs {
            assert_eq!(
                order_neighbours(*output_ord_src, Direction::Outgoing),
                output_ord_tgts
            );
        }
        for output_ord_tgt in &output_ord_tgts {
            assert_eq!(
                order_neighbours(*output_ord_tgt, Direction::Incoming),
                HashSet::from_iter(output_ord_srcs.union(&input_ord_srcs).copied())
            );
        }
        Ok(())
    }
}
