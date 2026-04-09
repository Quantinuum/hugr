use std::collections::BTreeSet;

use cool_asserts::assert_matches;
use rstest::{fixture, rstest};

use crate::builder::{endo_sig, inout_sig};
use crate::extension::prelude::{MakeTuple, UnpackTuple};
use crate::hugr::Patch;
use crate::hugr::internal::HugrMutInternals;
use crate::ops::Const;
use crate::ops::handle::DataflowParentID;
use crate::std_extensions::arithmetic::float_types::ConstF64;
use crate::std_extensions::logic::LogicOp;
use crate::type_row;
use crate::utils::test_quantum_extension::{cx_gate, rz_f64};
use crate::{
    builder::{
        BuildError, DFGBuilder, Dataflow, DataflowHugr, DataflowSubContainer, HugrBuilder,
        ModuleBuilder,
    },
    extension::prelude::{bool_t, qb_t},
    ops::handle::{DfgID, FuncID, NodeHandle},
    std_extensions::logic::test::and_op,
};

use super::*;

impl<N: HugrNode> SiblingSubgraph<N> {
    /// Create a sibling subgraph containing every node in a HUGR region.
    ///
    /// This will return an [`InvalidSubgraph::EmptySubgraph`] error if the
    /// subgraph is empty.
    fn from_sibling_graph(
        hugr: &impl HugrView<Node = N>,
        parent: N,
    ) -> Result<Self, InvalidSubgraph<N>> {
        let nodes = hugr.children(parent).collect_vec();
        if nodes.is_empty() {
            Err(InvalidSubgraph::EmptySubgraph)
        } else {
            Ok(Self {
                nodes,
                inputs: Vec::new(),
                outputs: Vec::new(),
                function_calls: Vec::new(),
            })
        }
    }
}

/// A Module with a single function from three qubits to three qubits.
/// The function applies a CX gate to the first two qubits and a Rz gate
/// (with a constant angle) to the last qubit.
fn build_hugr() -> Result<(Hugr, Node), BuildError> {
    let mut mod_builder = ModuleBuilder::new();
    let func = mod_builder.declare("test", Signature::new_endo([qb_t(), qb_t(), qb_t()]).into())?;
    let func_id = {
        let mut dfg = mod_builder.define_declaration(&func)?;
        let [w0, w1, w2] = dfg.input_wires_arr();
        let [w0, w1] = dfg.add_dataflow_op(cx_gate(), [w0, w1])?.outputs_arr();
        let c = dfg.add_load_const(Const::new(ConstF64::new(0.5).into()));
        let [w2] = dfg.add_dataflow_op(rz_f64(), [w2, c])?.outputs_arr();
        dfg.finish_with_outputs([w0, w1, w2])?
    };
    let hugr = mod_builder
        .finish_hugr()
        .map_err(|e| -> BuildError { e.into() })?;
    Ok((hugr, func_id.node()))
}

/// A bool to bool hugr with three subsequent NOT gates.
fn build_3not_hugr() -> Result<(Hugr, Node), BuildError> {
    let mut mod_builder = ModuleBuilder::new();
    let func = mod_builder.declare("test", Signature::new_endo([bool_t()]).into())?;
    let func_id = {
        let mut dfg = mod_builder.define_declaration(&func)?;
        let outs1 = dfg.add_dataflow_op(LogicOp::Not, dfg.input_wires())?;
        let outs2 = dfg.add_dataflow_op(LogicOp::Not, outs1.outputs())?;
        let outs3 = dfg.add_dataflow_op(LogicOp::Not, outs2.outputs())?;
        dfg.finish_with_outputs(outs3.outputs())?
    };
    let hugr = mod_builder
        .finish_hugr()
        .map_err(|e| -> BuildError { e.into() })?;
    Ok((hugr, func_id.node()))
}

/// A bool to (bool, bool) with multiports.
fn build_multiport_hugr() -> Result<(Hugr, Node), BuildError> {
    let mut mod_builder = ModuleBuilder::new();
    let func = mod_builder.declare(
        "test",
        Signature::new([bool_t()], vec![bool_t(), bool_t()]).into(),
    )?;
    let func_id = {
        let mut dfg = mod_builder.define_declaration(&func)?;
        let [b0] = dfg.input_wires_arr();
        let [b1] = dfg.add_dataflow_op(LogicOp::Not, [b0])?.outputs_arr();
        let [b2] = dfg.add_dataflow_op(LogicOp::Not, [b1])?.outputs_arr();
        dfg.finish_with_outputs([b1, b2])?
    };
    let hugr = mod_builder
        .finish_hugr()
        .map_err(|e| -> BuildError { e.into() })?;
    Ok((hugr, func_id.node()))
}

/// A HUGR with a copy
fn build_hugr_classical() -> Result<(Hugr, Node), BuildError> {
    let mut mod_builder = ModuleBuilder::new();
    let func = mod_builder.declare("test", Signature::new_endo([bool_t()]).into())?;
    let func_id = {
        let mut dfg = mod_builder.define_declaration(&func)?;
        let in_wire = dfg.input_wires().exactly_one().unwrap();
        let outs = dfg.add_dataflow_op(and_op(), [in_wire, in_wire])?;
        dfg.finish_with_outputs(outs.outputs())?
    };
    let hugr = mod_builder
        .finish_hugr()
        .map_err(|e| -> BuildError { e.into() })?;
    Ok((hugr, func_id.node()))
}

#[test]
fn construct_simple_replacement() -> Result<(), InvalidSubgraph> {
    let (mut hugr, func_root) = build_hugr().unwrap();
    let func = hugr.with_entrypoint(func_root);
    let sub = SiblingSubgraph::try_new_dataflow_subgraph::<_, FuncID<true>>(
        RootChecked::try_new(&func).expect("Root should be FuncDefn."),
    )?;
    assert!(sub.validate_default(&func).is_ok());

    let empty_dfg = {
        let builder = DFGBuilder::new(Signature::new_endo([qb_t(), qb_t(), qb_t()])).unwrap();
        let inputs = builder.input_wires();
        builder.finish_hugr_with_outputs(inputs).unwrap()
    };

    let rep = sub.create_simple_replacement(&func, empty_dfg).unwrap();

    assert_eq!(rep.subgraph().nodes().len(), 4);

    assert_eq!(hugr.num_nodes(), 8); // Module + Def + In + CX + Rz + Const + LoadConst + Out
    hugr.apply_patch(rep).unwrap();
    assert_eq!(hugr.num_nodes(), 4); // Module + Def + In + Out

    Ok(())
}

/// Make a sibling subgraph from a constant and a LoadConst node.
#[test]
fn construct_load_const_subgraph() -> Result<(), InvalidSubgraph> {
    let (hugr, func_root) = build_hugr().unwrap();

    let const_node = hugr
        .children(func_root)
        .find(|&n| hugr.get_optype(n).is_const())
        .unwrap();
    let load_const_node = hugr
        .children(func_root)
        .find(|&n| hugr.get_optype(n).is_load_constant())
        .unwrap();
    let nodes: BTreeSet<_> = BTreeSet::from_iter([const_node, load_const_node]);

    let sub = SiblingSubgraph::try_from_nodes(vec![const_node, load_const_node], &hugr)?;

    let subgraph_nodes: BTreeSet<_> = sub.nodes().iter().copied().collect();
    assert_eq!(subgraph_nodes, nodes);

    Ok(())
}

#[test]
fn test_signature() -> Result<(), InvalidSubgraph> {
    let (hugr, dfg) = build_hugr().unwrap();
    let func = hugr.with_entrypoint(dfg);
    let sub = SiblingSubgraph::try_new_dataflow_subgraph::<_, FuncID<true>>(
        RootChecked::try_new(&func).expect("Root should be FuncDefn."),
    )?;
    assert!(sub.validate_default(&func).is_ok());
    assert_eq!(
        sub.signature(&func),
        Signature::new_endo([qb_t(), qb_t(), qb_t()])
    );
    Ok(())
}

#[test]
fn construct_simple_replacement_invalid_signature() -> Result<(), InvalidSubgraph> {
    let (hugr, dfg) = build_hugr().unwrap();
    let func = hugr.with_entrypoint(dfg);
    let sub = SiblingSubgraph::from_sibling_graph(&hugr, dfg)?;

    let empty_dfg = {
        let builder = DFGBuilder::new(Signature::new_endo([qb_t()])).unwrap();
        let inputs = builder.input_wires();
        builder.finish_hugr_with_outputs(inputs).unwrap()
    };

    assert_matches!(
        sub.create_simple_replacement(&func, empty_dfg).unwrap_err(),
        InvalidReplacement::InvalidSignature { .. }
    );
    Ok(())
}

#[test]
fn convex_subgraph() {
    let (hugr, func_root) = build_hugr().unwrap();
    let func = hugr.with_entrypoint(func_root);
    assert_eq!(
        SiblingSubgraph::try_new_dataflow_subgraph::<_, FuncID<true>>(
            RootChecked::try_new(&func).expect("Root should be FuncDefn.")
        )
        .unwrap()
        .nodes()
        .len(),
        4
    );
}

#[test]
fn with_checker() {
    let (mut hugr, func_root) = build_hugr().unwrap();
    hugr.set_entrypoint(func_root);
    let mut hugr2 = hugr.clone();
    match hugr2.optype_mut(func_root) {
        OpType::FuncDefn(fd) => *fd.func_name_mut() = "test2".into(),
        _ => panic!(),
    };
    let func2 = hugr
        .insert_hugr(hugr.module_root(), hugr2)
        .inserted_entrypoint;
    hugr.validate().unwrap();

    let checker1 = SchedGraphChecker::new(hugr.scheduling_graph(func_root));
    let checker2 = SchedGraphChecker::new(hugr.scheduling_graph(func2));
    let sub1 = SiblingSubgraph::try_new_dataflow_subgraph::<_, FuncID<true>>(
        RootChecked::try_new(&hugr).expect("Root should be FuncDefn."),
    )
    .unwrap();
    sub1.validate_with_checker(&hugr, Some(&checker1)).unwrap();
    let e = sub1.validate_with_checker(&hugr, Some(&checker2));
    assert_eq!(
        e,
        Err(InvalidSubgraph::MismatchedCheckerParent {
            checker_parent: func2,
            subgraph_parent: func_root
        })
    );

    SiblingSubgraph::try_new_with_checker(
        sub1.inputs.clone(),
        sub1.outputs.clone(),
        &hugr,
        &checker1,
    )
    .unwrap();
    let e = SiblingSubgraph::try_new_with_checker(
        sub1.inputs.clone(),
        sub1.outputs.clone(),
        &hugr,
        &checker2,
    );
    assert_eq!(
        e,
        Err(InvalidSubgraph::MismatchedCheckerParent {
            checker_parent: func2,
            subgraph_parent: func_root
        })
    );

    SiblingSubgraph::try_from_nodes_with_checker(sub1.nodes.clone(), &hugr, &checker1).unwrap();
    let e = SiblingSubgraph::try_from_nodes_with_checker(sub1.nodes.clone(), &hugr, &checker2);
    assert_eq!(
        e,
        Err(InvalidSubgraph::MismatchedCheckerParent {
            checker_parent: func2,
            subgraph_parent: func_root
        })
    );
}

#[test]
fn convex_subgraph_2() {
    let (hugr, func_root) = build_hugr().unwrap();
    let [inp, out] = hugr.get_io(func_root).unwrap();
    let func = hugr.with_entrypoint(func_root);
    // All graph except input/output nodes
    SiblingSubgraph::try_new(
        hugr.node_outputs(inp)
            .take(2)
            .map(|p| hugr.linked_inputs(inp, p).collect_vec())
            .filter(|ps| !ps.is_empty())
            .collect(),
        hugr.node_inputs(out)
            .take(2)
            .filter_map(|p| hugr.single_linked_output(out, p))
            .collect(),
        &func,
    )
    .unwrap();
}

#[test]
fn degen_boundary() {
    let (hugr, func_root) = build_hugr().unwrap();
    let func = hugr.with_entrypoint(func_root);
    let [inp, _] = hugr.get_io(func_root).unwrap();
    let first_cx_edge = hugr.node_outputs(inp).next().unwrap();
    // All graph but one edge
    assert_matches!(
        SiblingSubgraph::try_new(
            vec![
                hugr.linked_ports(inp, first_cx_edge)
                    .map(|(n, p)| (n, p.as_incoming().unwrap()))
                    .collect()
            ],
            vec![(inp, first_cx_edge)],
            &func,
        ),
        Err(InvalidSubgraph::InvalidBoundary(
            InvalidSubgraphBoundary::DisconnectedBoundaryPort(_, _)
        ))
    );
}

#[test]
fn non_convex_subgraph() {
    let (hugr, func_root) = build_3not_hugr().unwrap();
    let func = hugr.with_entrypoint(func_root);
    let [inp, _out] = hugr.get_io(func_root).unwrap();
    let not1 = hugr.output_neighbours(inp).exactly_one().ok().unwrap();
    let not2 = hugr.output_neighbours(not1).exactly_one().ok().unwrap();
    let not3 = hugr.output_neighbours(not2).exactly_one().ok().unwrap();
    let not1_inp = hugr.node_inputs(not1).next().unwrap();
    let not1_out = hugr.node_outputs(not1).next().unwrap();
    let not3_inp = hugr.node_inputs(not3).next().unwrap();
    let not3_out = hugr.node_outputs(not3).next().unwrap();
    assert_matches!(
        SiblingSubgraph::try_new(
            vec![vec![(not1, not1_inp)], vec![(not3, not3_inp)]],
            vec![(not1, not1_out), (not3, not3_out)],
            &func
        ),
        Err(InvalidSubgraph::NotConvex)
    );
}

/// A subgraphs mixed with multiports caused a `NonConvex` error.
/// <https://github.com/CQCL/hugr/issues/1294>
#[test]
fn convex_multiports() {
    let (hugr, func_root) = build_multiport_hugr().unwrap();
    let [inp, out] = hugr.get_io(func_root).unwrap();
    let not1 = hugr.output_neighbours(inp).exactly_one().ok().unwrap();
    let not2 = hugr
        .output_neighbours(not1)
        .filter(|&n| n != out)
        .exactly_one()
        .ok()
        .unwrap();

    let subgraph = SiblingSubgraph::try_from_nodes([not1, not2], &hugr).unwrap();
    assert_eq!(subgraph.nodes(), [not1, not2]);
}

#[test]
fn invalid_boundary() {
    let (hugr, func_root) = build_hugr().unwrap();
    let func = hugr.with_entrypoint(func_root);
    let [inp, out] = hugr.get_io(func_root).unwrap();
    let cx_edges_in = hugr.node_outputs(inp);
    let cx_edges_out = hugr.node_inputs(out);
    // All graph but the CX
    assert_matches!(
        SiblingSubgraph::try_new(
            cx_edges_out.map(|p| vec![(out, p)]).collect(),
            cx_edges_in.map(|p| (inp, p)).collect(),
            &func,
        ),
        Err(InvalidSubgraph::InvalidBoundary(
            InvalidSubgraphBoundary::DisconnectedBoundaryPort(_, _)
        ))
    );
}

#[test]
fn preserve_signature() {
    let (hugr, func_root) = build_hugr_classical().unwrap();
    let func_graph = hugr.with_entrypoint(func_root);
    let func = SiblingSubgraph::try_new_dataflow_subgraph::<_, FuncID<true>>(
        RootChecked::try_new(&func_graph).expect("Root should be FuncDefn."),
    )
    .unwrap();
    let func_defn = hugr.get_optype(func_root).as_func_defn().unwrap();
    assert_eq!(func_defn.signature(), &func.signature(&func_graph).into());
}

#[test]
fn extract_subgraph() {
    let (hugr, func_root) = build_hugr().unwrap();
    let func_graph = hugr.with_entrypoint(func_root);
    let subgraph = SiblingSubgraph::try_new_dataflow_subgraph::<_, FuncID<true>>(
        RootChecked::try_new(&func_graph).expect("Root should be FuncDefn."),
    )
    .unwrap();
    let extracted = subgraph.extract_subgraph(&hugr, "region");

    extracted.validate().unwrap();
}

#[test]
fn edge_both_output_and_copy() {
    // https://github.com/CQCL/hugr/issues/518
    let one_bit = vec![bool_t()];
    let two_bit = vec![bool_t(), bool_t()];

    let mut builder = DFGBuilder::new(inout_sig(one_bit.clone(), two_bit.clone())).unwrap();
    let inw = builder.input_wires().exactly_one().unwrap();
    let outw1 = builder
        .add_dataflow_op(LogicOp::Not, [inw])
        .unwrap()
        .out_wire(0);
    let outw2 = builder
        .add_dataflow_op(and_op(), [inw, outw1])
        .unwrap()
        .outputs();
    let outw = [outw1].into_iter().chain(outw2);
    let h = builder.finish_hugr_with_outputs(outw).unwrap();
    let subg = SiblingSubgraph::try_new_dataflow_subgraph::<_, DfgID>(
        RootChecked::try_new(&h).expect("Root should be DFG."),
    )
    .unwrap();
    assert_eq!(subg.nodes().len(), 2);
}

#[test]
fn test_unconnected() {
    // test a replacement on a subgraph with a discarded output
    let mut b = DFGBuilder::new(Signature::new([bool_t()], type_row![])).unwrap();
    let inw = b.input_wires().exactly_one().unwrap();
    let not_n = b.add_dataflow_op(LogicOp::Not, [inw]).unwrap();
    // Unconnected output, discarded
    let mut h = b.finish_hugr_with_outputs([]).unwrap();

    let subg = SiblingSubgraph::from_node(not_n.node(), &h);

    assert_eq!(subg.nodes().len(), 1);
    //  TODO create a valid replacement
    let replacement = {
        let mut rep_b = DFGBuilder::new(Signature::new_endo([bool_t()])).unwrap();
        let inw = rep_b.input_wires().exactly_one().unwrap();

        let not_n = rep_b.add_dataflow_op(LogicOp::Not, [inw]).unwrap();

        rep_b.finish_hugr_with_outputs(not_n.outputs()).unwrap()
    };
    let rep = subg.create_simple_replacement(&h, replacement).unwrap();
    rep.apply(&mut h).unwrap();
}

/// Test the behaviour of the sibling subgraph when built from a single
/// node.
#[test]
fn single_node_subgraph() {
    // A hugr with a single NOT operation, with disconnected output.
    let mut b = DFGBuilder::new(Signature::new([bool_t()], type_row![])).unwrap();
    let inw = b.input_wires().exactly_one().unwrap();
    let not_n = b.add_dataflow_op(LogicOp::Not, [inw]).unwrap();
    // Unconnected output, discarded
    let h = b.finish_hugr_with_outputs([]).unwrap();

    // When built with `from_node`, the subgraph's signature is the same as the
    // node's. (bool input, bool output)
    let subg = SiblingSubgraph::from_node(not_n.node(), &h);
    assert_eq!(subg.nodes().len(), 1);
    assert_eq!(
        subg.signature(&h).io(),
        Signature::new(vec![bool_t()], vec![bool_t()]).io()
    );

    // `from_nodes` is different, is it only uses incoming and outgoing edges to
    // compute the signature. In this case, the output is disconnected, so
    // it is not part of the subgraph signature.
    let subg = SiblingSubgraph::try_from_nodes([not_n.node()], &h).unwrap();
    assert_eq!(subg.nodes().len(), 1);
    assert_eq!(
        subg.signature(&h).io(),
        Signature::new(vec![bool_t()], vec![]).io()
    );
}

/// Test the behaviour of the sibling subgraph when built from a single
/// node with no inputs or outputs.
#[test]
fn singleton_disconnected_subgraph() {
    // A hugr with some empty MakeTuple operations.
    let op = MakeTuple::new(type_row![]);

    let mut b = DFGBuilder::new(Signature::new_endo(type_row![])).unwrap();
    let _mk_tuple_1 = b.add_dataflow_op(op.clone(), []).unwrap();
    let mk_tuple_2 = b.add_dataflow_op(op.clone(), []).unwrap();
    let _mk_tuple_3 = b.add_dataflow_op(op, []).unwrap();
    // Unconnected output, discarded
    let h = b.finish_hugr_with_outputs([]).unwrap();

    // When built with `try_from_nodes`, the subgraph's signature is the same as the
    // node's. (empty input, tuple output)
    let subg = SiblingSubgraph::from_node(mk_tuple_2.node(), &h);
    assert_eq!(subg.nodes().len(), 1);
    assert_eq!(
        subg.signature(&h).io(),
        Signature::new(type_row![], vec![Type::new_tuple(type_row![])]).io()
    );

    // `from_nodes` is different, is it only uses incoming and outgoing edges to
    // compute the signature. In this case, the output is disconnected, so
    // it is not part of the subgraph signature.
    let subg = SiblingSubgraph::try_from_nodes([mk_tuple_2.node()], &h).unwrap();
    assert_eq!(subg.nodes().len(), 1);
    assert_eq!(
        subg.signature(&h).io(),
        Signature::new_endo(type_row![]).io()
    );
}

/// Run `try_from_nodes` including some complete graph components.
#[test]
fn partially_connected_subgraph() {
    // A hugr with some empty MakeTuple operations.
    let tuple_op = MakeTuple::new(type_row![]);
    let untuple_op = UnpackTuple::new(type_row![]);
    let tuple_t = Type::new_tuple(type_row![]);

    let mut b = DFGBuilder::new(Signature::new(type_row![], vec![tuple_t.clone()])).unwrap();
    let mk_tuple_1 = b.add_dataflow_op(tuple_op.clone(), []).unwrap();
    let untuple_1 = b
        .add_dataflow_op(untuple_op.clone(), [mk_tuple_1.out_wire(0)])
        .unwrap();
    let mk_tuple_2 = b.add_dataflow_op(tuple_op.clone(), []).unwrap();
    let _mk_tuple_3 = b.add_dataflow_op(tuple_op, []).unwrap();
    // Output the 2nd tuple output
    let h = b
        .finish_hugr_with_outputs([mk_tuple_2.out_wire(0)])
        .unwrap();

    let subgraph_nodes = [mk_tuple_1.node(), mk_tuple_2.node(), untuple_1.node()];

    // `try_from_nodes` uses incoming and outgoing edges to compute the signature.
    let subg = SiblingSubgraph::try_from_nodes(subgraph_nodes, &h).unwrap();
    assert_eq!(subg.nodes().len(), 3);
    assert_eq!(
        subg.signature(&h).io(),
        Signature::new(type_row![], vec![tuple_t]).io()
    );
}

#[test]
fn test_set_outgoing_ports() {
    let (hugr, func_root) = build_3not_hugr().unwrap();
    let [inp, out] = hugr.get_io(func_root).unwrap();
    let not1 = hugr.output_neighbours(inp).exactly_one().ok().unwrap();
    let not1_out = hugr.node_outputs(not1).next().unwrap();

    // Create a subgraph with just the NOT gate
    let mut subgraph = SiblingSubgraph::from_node(not1, &hugr);

    // Initially should have one output
    assert_eq!(subgraph.outgoing_ports().len(), 1);

    // Try to set two outputs by copying the existing one
    let new_outputs = vec![(not1, not1_out), (not1, not1_out)];
    assert!(subgraph.set_outgoing_ports(new_outputs, &hugr).is_ok());

    // Should now have two outputs
    assert_eq!(subgraph.outgoing_ports().len(), 2);

    // Try to set an invalid output (from a different node)
    let invalid_outputs = vec![(not1, not1_out), (out, 2.into())];
    assert!(matches!(
        subgraph.set_outgoing_ports(invalid_outputs, &hugr),
        Err(InvalidOutputPorts::UnknownOutput { .. })
    ));

    // Should still have two outputs from before
    assert_eq!(subgraph.outgoing_ports().len(), 2);
}

#[test]
fn test_set_outgoing_ports_linear() {
    let (hugr, func_root) = build_hugr().unwrap();
    let [inp, _out] = hugr.get_io(func_root).unwrap();
    let rz = hugr.output_neighbours(inp).nth(2).unwrap();
    let rz_out = hugr.node_outputs(rz).next().unwrap();

    // Create a subgraph with just the CX gate
    let mut subgraph = SiblingSubgraph::from_node(rz, &hugr);

    // Initially should have one output
    assert_eq!(subgraph.outgoing_ports().len(), 1);

    // Try to set two outputs by copying the existing one (should fail for linear
    // ports)
    let new_outputs = vec![(rz, rz_out), (rz, rz_out)];
    assert!(matches!(
        subgraph.set_outgoing_ports(new_outputs, &hugr),
        Err(InvalidOutputPorts::NonUniqueLinear)
    ));

    // Should still have one output
    assert_eq!(subgraph.outgoing_ports().len(), 1);
}

#[test]
fn test_try_from_nodes_with_intervals() {
    let (hugr, func_root) = build_3not_hugr().unwrap();
    let line_checker = LineConvexChecker::new(&hugr, func_root);
    let [inp, _out] = hugr.get_io(func_root).unwrap();
    let not1 = hugr.output_neighbours(inp).exactly_one().ok().unwrap();
    let not2 = hugr.output_neighbours(not1).exactly_one().ok().unwrap();

    let intervals = line_checker.get_intervals_from_nodes([not1, not2]).unwrap();
    let subgraph =
        SiblingSubgraph::try_from_nodes_with_intervals([not1, not2], &intervals, &line_checker)
            .unwrap();
    let exp_subgraph = SiblingSubgraph::try_from_nodes([not1, not2], &hugr).unwrap();

    assert_eq!(subgraph, exp_subgraph);
    assert_eq!(
        line_checker.nodes_in_intervals(&intervals).collect_vec(),
        [not1, not2]
    );

    let intervals2 = line_checker
        .get_intervals_from_boundary_ports([
            (not1, IncomingPort::from(0).into()),
            (not2, OutgoingPort::from(0).into()),
        ])
        .unwrap();
    let subgraph2 =
        SiblingSubgraph::try_from_nodes_with_intervals([not1, not2], &intervals2, &line_checker)
            .unwrap();
    assert_eq!(subgraph2, exp_subgraph);
}

#[test]
fn test_validate() {
    let (hugr, func_root) = build_3not_hugr().unwrap();
    let func = hugr.with_entrypoint(func_root);
    let checker = SchedGraphChecker::new(func.scheduling_graph(func_root));
    let [inp, _out] = hugr.get_io(func_root).unwrap();
    let not1 = hugr.output_neighbours(inp).exactly_one().ok().unwrap();
    let not2 = hugr.output_neighbours(not1).exactly_one().ok().unwrap();
    let not3 = hugr.output_neighbours(not2).exactly_one().ok().unwrap();

    // A valid boundary, and convex
    let sub = SiblingSubgraph::new_unchecked(
        vec![vec![(not1, 0.into())]],
        vec![(not2, 0.into())],
        vec![],
        vec![not1, not2],
    );
    assert_eq!(sub.validate_skip_convexity(&func), Ok(()));
    assert_eq!(sub.validate_skip_convexity(&func), Ok(()));
    assert_eq!(sub.validate_with_checker(&func, Some(&checker)), Ok(()));

    // A valid boundary, but not convex
    let sub = SiblingSubgraph::new_unchecked(
        vec![vec![(not1, 0.into())], vec![(not3, 0.into())]],
        vec![(not1, 0.into()), (not3, 0.into())],
        vec![],
        vec![not1, not3],
    );
    assert_eq!(sub.validate_skip_convexity(&func), Ok(()));
    assert_eq!(sub.validate_default(&func), Err(InvalidSubgraph::NotConvex));
    assert_eq!(
        sub.validate_with_checker(&func, Some(&checker)),
        Err(InvalidSubgraph::NotConvex)
    );

    // An invalid boundary (missing an input)
    let sub = SiblingSubgraph::new_unchecked(
        vec![vec![(not1, 0.into())]],
        vec![(not1, 0.into()), (not3, 0.into())],
        vec![],
        vec![not1, not3],
    );
    assert_eq!(
        sub.validate_skip_convexity(&func),
        Err(InvalidSubgraph::InvalidNodeSet)
    );
}

#[fixture]
pub(crate) fn hugr_call_subgraph() -> Hugr {
    let mut builder = ModuleBuilder::new();
    let decl_node = builder
        .declare("test", endo_sig([bool_t()]).into())
        .unwrap();
    let mut main = builder
        .define_function("main", endo_sig([bool_t()]))
        .unwrap();
    let [bool] = main.input_wires_arr();

    let [bool] = main
        .add_dataflow_op(LogicOp::Not, [bool])
        .unwrap()
        .outputs_arr();

    // Chain two calls to the same function
    let [bool] = main.call(&decl_node, &[], [bool]).unwrap().outputs_arr();
    let [bool] = main.call(&decl_node, &[], [bool]).unwrap().outputs_arr();

    let main_def = main.finish_with_outputs([bool]).unwrap();

    let mut hugr = builder.finish_hugr().unwrap();
    hugr.set_entrypoint(main_def.node());
    hugr
}

#[rstest]
fn test_call_subgraph_from_dfg(hugr_call_subgraph: Hugr) {
    let subg = SiblingSubgraph::try_new_dataflow_subgraph::<_, DataflowParentID>(
        RootChecked::try_new(&hugr_call_subgraph).expect("Root should be DFG container."),
    )
    .unwrap();

    assert_eq!(subg.function_calls.len(), 1);
    assert_eq!(subg.function_calls[0].len(), 2);
}

#[rstest]
fn test_call_subgraph_from_nodes(hugr_call_subgraph: Hugr) {
    let call_nodes = hugr_call_subgraph
        .children(hugr_call_subgraph.entrypoint())
        .filter(|&n| hugr_call_subgraph.get_optype(n).is_call())
        .collect_vec();

    let subg = SiblingSubgraph::try_from_nodes(call_nodes.clone(), &hugr_call_subgraph).unwrap();
    assert_eq!(subg.function_calls.len(), 1);
    assert_eq!(subg.function_calls[0].len(), 2);

    let subg =
        SiblingSubgraph::try_from_nodes(call_nodes[0..1].to_owned(), &hugr_call_subgraph).unwrap();
    assert_eq!(subg.function_calls.len(), 1);
    assert_eq!(subg.function_calls[0].len(), 1);
}

#[rstest]
fn test_call_subgraph_from_boundary(hugr_call_subgraph: Hugr) {
    let call_nodes = hugr_call_subgraph
        .children(hugr_call_subgraph.entrypoint())
        .filter(|&n| hugr_call_subgraph.get_optype(n).is_call())
        .collect_vec();
    let not_node = hugr_call_subgraph
        .children(hugr_call_subgraph.entrypoint())
        .filter(|&n| hugr_call_subgraph.get_optype(n) == &LogicOp::Not.into())
        .exactly_one()
        .ok()
        .unwrap();

    let subg = SiblingSubgraph::try_new(
        vec![
            vec![(not_node, IncomingPort::from(0))],
            call_nodes
                .iter()
                .map(|&n| (n, IncomingPort::from(1)))
                .collect_vec(),
        ],
        vec![(call_nodes[1], OutgoingPort::from(0))],
        &hugr_call_subgraph,
    )
    .unwrap();

    assert_eq!(subg.function_calls.len(), 1);
    assert_eq!(subg.function_calls[0].len(), 2);
}
