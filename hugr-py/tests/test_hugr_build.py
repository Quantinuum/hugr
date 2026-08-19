from __future__ import annotations

import html
from copy import deepcopy

import pytest

import hugr.ext as ext
import hugr.ops as ops
import hugr.tys as tys
import hugr.val as val
from hugr.build.dfg import Dfg, Function, _ancestral_sibling
from hugr.build.function import Module
from hugr.hugr import Hugr
from hugr.hugr.node_port import Node
from hugr.hugr.render import RenderConfig
from hugr.ops import NoConcreteFunc
from hugr.package import Package
from hugr.std.collections.array import Array
from hugr.std.int import INT_T, DivMod, IntVal, int_t
from hugr.std.logic import Not

from .conftest import QUANTUM_EXT, H, validate


def test_stable_indices():
    h = Hugr(ops.DFG([]))

    nodes = [h.add_node(Not, num_outs=1) for _ in range(3)]
    assert len(h) == 8
    assert len(list(h.descendants())) == 4
    assert list(iter(h)) == [Node(i) for i in range(8)]
    assert all(data is not None for node, data in h.nodes())

    assert len(list(nodes[0].outputs())) == 1
    assert list(nodes[0]) == list(nodes[0].outputs())

    h.add_link(nodes[0].out(0), nodes[1].inp(0))
    assert h.children() == nodes

    assert h.num_outgoing(nodes[0]) == 1
    assert h.num_incoming(nodes[1]) == 1

    assert nodes[1] in h.children(h.entrypoint)
    assert h.delete_node(nodes[1]) is not None
    assert h._nodes[nodes[1].idx] is None
    assert nodes[1] not in h.children(h.entrypoint)

    assert len(h) == 7
    assert len(h._nodes) == 8
    assert h._free_nodes == [nodes[1]]

    assert h.num_outgoing(nodes[0]) == 0
    assert h.num_incoming(nodes[1]) == 0

    with pytest.raises(KeyError):
        _ = h[nodes[1]]
    with pytest.raises(KeyError):
        _ = h[Node(46)]

    new_n = h.add_node(Not)
    assert new_n == nodes[1]

    assert len(h) == 8
    assert h._free_nodes == []
    assert list(iter(h)) == [Node(i) for i in range(len(h))]
    assert all(data is not None for node, data in h.nodes())


def simple_id() -> Dfg:
    h = Dfg(tys.Qubit, tys.Qubit)
    a, b = h.inputs()
    h.set_outputs(a, b)
    return h


def test_simple_id(snapshot):
    hugr = simple_id().hugr
    validate(hugr, snap=snapshot)


def test_metadata(snapshot):
    h = Dfg(tys.Bool)
    h.metadata["name"] = "simple_id"

    (b,) = h.inputs()
    b = h.add_op(Not, b, metadata={"name": "not"})

    h.set_outputs(b)
    validate(h.hugr, snap=snapshot)


def test_multiport(snapshot):
    h = Dfg(tys.Bool)
    (a,) = h.inputs()
    h.set_outputs(a, a)
    in_n, ou_n = h.input_node, h.output_node
    assert list(h.hugr.outgoing_links(in_n)) == [
        (in_n.out(0), [ou_n.inp(0), ou_n.inp(1)]),
    ]

    assert list(h.hugr.incoming_links(ou_n)) == [
        (ou_n.inp(0), [in_n.out(0)]),
        (ou_n.inp(1), [in_n.out(0)]),
    ]

    assert list(h.hugr.linked_ports(in_n.out(0))) == [
        ou_n.inp(0),
        ou_n.inp(1),
    ]

    assert list(h.hugr.linked_ports(ou_n.inp(0))) == [in_n.out(0)]
    validate(h.hugr, snap=snapshot)


def test_sparse_subports():
    dfg = Dfg(tys.Bool)
    h = dfg.hugr
    src = dfg.input_node.out(0)
    dst = dfg.output_node
    dst_0, dst_1, dst_2 = dst.inp(0), dst.inp(1), dst.inp(2)

    h.add_link(src, dst_0)
    h.add_link(src, dst_1)
    h.delete_link(src, dst_0)

    assert list(h.linked_ports(src)) == [dst_1]
    assert list(h.linked_ports(dst_1)) == [src]

    h.add_link(src, dst_2)
    assert list(h.linked_ports(src)) == [dst_1, dst_2]

    h.delete_link(src, dst_1)
    assert list(h.linked_ports(src)) == [dst_2]


def test_delete_node_with_fanout():
    h = Hugr(ops.DFG([]))
    src = h.add_node(Not, num_outs=1)
    dst_0 = h.add_node(Not)
    dst_1 = h.add_node(Not)

    h.add_link(src.out(0), dst_0.inp(0))
    h.add_link(src.out(0), dst_1.inp(0))
    h.delete_node(src)

    assert list(h.links()) == []
    assert list(h.linked_ports(dst_0.inp(0))) == []
    assert list(h.linked_ports(dst_1.inp(0))) == []

    replacement = h.add_node(Not, num_outs=1)
    assert replacement == src
    h.add_link(replacement.out(0), dst_0.inp(0))
    assert list(h.linked_ports(replacement.out(0))) == [dst_0.inp(0)]
    assert list(h.linked_ports(dst_0.inp(0))) == [replacement.out(0)]


def test_link_allocation_history_does_not_affect_equality():
    h = Hugr(ops.DFG([]))
    src = h.add_node(Not, num_outs=1)
    dst = h.add_node(Not)
    h.add_link(src.out(0), dst.inp(0))
    equivalent = deepcopy(h)

    h.delete_link(src.out(0), dst.inp(0))
    h.add_link(src.out(0), dst.inp(0))

    assert h == equivalent


def test_add_op(snapshot):
    h = Dfg(tys.Bool)
    (a,) = h.inputs()
    nt = h.add_op(Not, a)
    h.set_outputs(nt)

    validate(h.hugr, snap=snapshot)


def test_tuple(snapshot):
    row = [tys.Bool, tys.Qubit]
    h = Dfg(*row)
    a, b = h.inputs()
    t = h.add(ops.MakeTuple()(a, b))
    a, b = h.add(ops.UnpackTuple()(t))
    h.set_outputs(a, b)

    validate(h.hugr, snap=snapshot)

    h1 = Dfg(*row)
    a, b = h1.inputs()
    mt = h1.add_op(ops.MakeTuple(), a, b)
    a, b = h1.add_op(ops.UnpackTuple(), mt)[0, 1]
    h1.set_outputs(a, b)

    assert h.hugr._to_serial() == h1.hugr._to_serial()


def test_multi_out(snapshot):
    h = Dfg(INT_T, INT_T)
    a, b = h.inputs()
    a, b = h.add(DivMod(a, b))
    h.set_outputs(a, b)
    validate(h.hugr, snap=snapshot)


def test_insert():
    h1 = Dfg(tys.Bool)
    (a1,) = h1.inputs()
    nt = h1.add(Not(a1))
    h1.set_outputs(nt)

    assert len(h1.hugr) == 8

    new_h = Hugr(ops.DFG([]))
    mapping = h1.hugr.insert_hugr(new_h, h1.hugr.entrypoint)
    assert mapping == {new_h.entrypoint: Node(8)}


def test_insert_nested(snapshot):
    h1 = Dfg(tys.Bool)
    (a1,) = h1.inputs()
    nt = h1.add(Not(a1))
    h1.set_outputs(nt)

    h = Dfg(tys.Bool)
    (a,) = h.inputs()
    nested = h.insert_nested(h1, a)
    h.set_outputs(nested)
    assert len(h.hugr.children(nested)) == 3
    validate(h.hugr, snap=snapshot)


def test_build_nested(snapshot):
    h = Dfg(tys.Bool)
    (a,) = h.inputs()

    with h.add_nested(a) as nested:
        (a1,) = nested.inputs()
        nt = nested.add(Not(a1))
        nested.set_outputs(nt)

    assert len(h.hugr.children(nested)) == 3
    h.set_outputs(nested)

    validate(h.hugr, snap=snapshot)


def test_build_inter_graph(snapshot):
    # Possibly a bit redundant now, really we're just testing that we *don't* do
    # anything special anymore, following https://github.com/Quantinuum/hugr/pull/2951.
    h = Dfg(tys.Bool, tys.Bool)
    (a, b) = h.inputs()
    with h.add_nested() as nested:
        nt = nested.add(Not(a))
        nested.set_outputs(nt)

    h.set_outputs(nested, b)

    validate(h.hugr, snap=snapshot)

    assert h.hugr.num_outgoing(h.input_node) == 2
    assert len(list(h.hugr.outgoing_order_links(h.input_node))) == 0
    assert len(list(h.hugr.incoming_order_links(nested))) == 0
    assert len(list(h.hugr.incoming_order_links(h.output_node))) == 0


def test_ancestral_sibling():
    h = Dfg(tys.Bool)
    (a,) = h.inputs()
    with h.add_nested() as nested:
        nt = nested.add(Not(a))

    assert _ancestral_sibling(h.hugr, h.input_node, nt) == nested.parent_node


@pytest.mark.parametrize(
    "val",
    [
        val.Sum(1, tys.Sum([[INT_T], [tys.Bool, INT_T]]), [val.TRUE, IntVal(34)]),
        val.Tuple(val.TRUE, IntVal(23)),
    ],
)
def test_vals(val: val.Value):
    d = Dfg()
    d.set_outputs(d.load(val))

    validate(d.hugr)


@pytest.mark.parametrize("direct_call", [True, False])
def test_poly_function(direct_call: bool) -> None:
    mod = Module()
    f_id = mod.declare_function(
        "id",
        tys.PolyFuncType(
            [tys.TypeTypeParam(tys.TypeBound.Linear)],
            tys.FunctionType.endo([tys.Variable(0, tys.TypeBound.Linear)]),
        ),
    )

    f_main = mod.define_main([tys.Qubit])
    q = f_main.input_node[0]
    # for now concrete instantiations have to be provided.
    instantiation = tys.FunctionType.endo([tys.Qubit])
    type_args = [tys.Qubit.type_arg()]
    if direct_call:
        with pytest.raises(NoConcreteFunc, match="Missing instantiation"):
            f_main.call(f_id, q)
        call = f_main.call(f_id, q, instantiation=instantiation, type_args=type_args)
    else:
        with pytest.raises(NoConcreteFunc, match="Missing instantiation"):
            f_main.load_function(f_id)
        load = f_main.load_function(
            f_id, instantiation=instantiation, type_args=type_args
        )
        call = f_main.add(ops.CallIndirect()(load, q))

    f_main.set_outputs(call)

    validate(mod.hugr)


def test_literals() -> None:
    mod = Module()

    func = mod.declare_function(
        "literals",
        tys.PolyFuncType(
            [
                tys.StringParam(),
                tys.BoundedNatParam(),
                tys.BytesParam(),
                tys.FloatParam(),
            ],
            tys.FunctionType.endo([tys.Qubit]),
        ),
    )

    caller = mod.define_function("caller", [tys.Qubit], [tys.Qubit])
    call = caller.call(
        func,
        caller.inputs()[0],
        instantiation=tys.FunctionType.endo([tys.Qubit]),
        type_args=[
            tys.StringArg("string"),
            tys.BoundedNatArg(42),
            tys.BytesArg(b"HUGR"),
            tys.FloatArg(0.9),
        ],
    )
    caller.set_outputs(call)

    validate(mod.hugr)


def test_const_type() -> None:
    mod = Module()

    mod.declare_function(
        "const_type",
        tys.PolyFuncType(
            [tys.ConstParam(tys.Qubit)],
            tys.FunctionType([], [tys.Qubit]),
        ),
    )

    validate(mod.hugr)


@pytest.mark.parametrize("direct_call", [True, False])
def test_mono_function(direct_call: bool) -> None:
    mod = Module()
    f_id = mod.define_function("id", [tys.Qubit])
    f_id.set_outputs(f_id.input_node[0])

    f_main = mod.define_main([tys.Qubit])
    q = f_main.input_node[0]
    # monomorphic functions don't need instantiation specified
    if direct_call:
        call = f_main.call(f_id, q)
    else:
        load = f_main.load_function(f_id)
        call = f_main.add(ops.CallIndirect()(load, q))
    f_main.set_outputs(call)

    validate(mod.hugr)


def test_static_output() -> None:
    mod = Module()

    mod.declare_function(
        "declared",
        tys.PolyFuncType(
            [],
            tys.FunctionType.endo([]),
        ),
    )

    func = mod.define_function("defined", [], [])
    func.declare_outputs([])
    func.set_outputs()

    validate(mod.hugr)


def test_function_dfg() -> None:
    d = Dfg(tys.Qubit)

    f_id = d.module_root_builder().define_function("id", [tys.Qubit])
    f_id.set_outputs(f_id.input_node[0])

    (q,) = d.inputs()
    call = d.call(f_id, q)
    d.set_outputs(call)

    validate(d.hugr)


def test_recursive_function(snapshot) -> None:
    mod = Module()

    f_recursive = mod.define_function("recurse", [tys.Qubit])
    f_recursive.declare_outputs([tys.Qubit])
    call = f_recursive.call(f_recursive, f_recursive.input_node[0])
    f_recursive.set_outputs(call)

    validate(mod.hugr, snap=snapshot)


def test_invalid_recursive_function() -> None:
    mod = Module()

    f_recursive = mod.define_function("recurse", [tys.Bool], [tys.Qubit])
    f_recursive.call(f_recursive, f_recursive.input_node[0])

    with pytest.raises(ValueError, match="The function has fixed output type"):
        f_recursive.set_outputs(f_recursive.input_node[0])


@pytest.mark.skip("Value::Function is deprecated and not supported by model encoding.")
def test_higher_order(snapshot) -> None:
    noop_fn = Dfg(tys.Qubit)
    noop_fn.set_outputs(noop_fn.add(ops.Noop()(noop_fn.input_node[0])))

    d = Dfg(tys.Qubit)
    (q,) = d.inputs()
    f_val = d.load(val.Function(noop_fn.hugr))
    call = d.add(ops.CallIndirect()(f_val, q))[0]
    d.add_state_order(d.input_node, f_val)
    d.set_outputs(call)

    validate(d.hugr, snap=snapshot)


def test_state_order() -> None:
    mod = Module()
    f_id = mod.define_function("id", [tys.Bool])
    f_id.set_outputs(f_id.input_node[0])

    f_main = mod.define_main([tys.Bool])
    b = f_main.input_node[0]
    call1 = f_main.call(f_id, b)
    f_main.add_state_order(call1, f_main.output_node)
    # implicit discard of bool to test state order port logic
    f_main.set_outputs()
    validate(mod.hugr)


def test_alias() -> None:
    mod = Module()
    _dfn = mod.add_alias_defn("my_int", INT_T)
    _dcl = mod.add_alias_decl("my_bool", tys.TypeBound.Copyable)

    validate(mod.hugr)


# https://github.com/CQCL/hugr/issues/1625
def test_dfg_unpack() -> None:
    dfg = Dfg(tys.Tuple(tys.Bool, tys.Bool))
    bool1, _unused_bool2 = dfg.add_op(ops.UnpackTuple(), *dfg.inputs())
    cond = dfg.add_conditional(bool1)
    with cond.add_case(0) as case:
        case.set_outputs(bool1)
    with cond.add_case(1) as case:
        case.set_outputs(bool1)
    dfg.set_outputs(*cond.outputs())

    validate(dfg.hugr)


def test_option() -> None:
    dfg = Dfg(tys.Bool)
    b = dfg.inputs()[0]

    dfg.add_op(ops.Some(tys.Bool), b)

    dfg.set_outputs(b)

    validate(dfg.hugr)


# a helper for the toposort tests
@pytest.fixture
def simple_fn() -> Function:
    f = Function("prepare_qubit", [tys.Bool, tys.Qubit])
    [b, q] = f.inputs()

    h = f.add_op(H, q)
    q = h.out(0)

    not_node = f.add_op(Not, b)

    f.set_outputs(q, not_node, b)
    validate(Package([f.hugr], [QUANTUM_EXT]))
    return f


# https://github.com/CQCL/hugr/issues/2350
def test_toposort(simple_fn: Function) -> None:
    nodes = list(simple_fn.hugr)
    func_node = nodes[1]

    sorted_nodes = list(simple_fn.hugr.sorted_region_nodes(func_node))
    assert set(sorted_nodes) == set(simple_fn.hugr.children(simple_fn))
    assert sorted_nodes[0] == simple_fn.input_node
    assert sorted_nodes[-1] == simple_fn.output_node


def test_toposort_error(simple_fn: Function) -> None:
    # Test that we get an error if we toposort an invalid hugr containing a cycle
    nodes = list(simple_fn.hugr)
    func_node = nodes[1]

    # Add a loop, invalidating the HUGR
    simple_fn.hugr.add_link(nodes[4].out_port(), nodes[4].inp(0))
    with pytest.raises(
        ValueError, match="Graph contains a cycle. No topological ordering exists."
    ):
        list(simple_fn.hugr.sorted_region_nodes(func_node))


def test_html_labels(snapshot) -> None:
    """Ensures that HTML-like labels can be processed correctly by both the builder and
    the renderer.
    """
    f = Function(
        "<jupyter-notebook>",
        [tys.Bool],
    )
    f.metadata["label"] = "<b>Bold Label</b>"
    f.metadata["<other-label>"] = "<i>Italic Label</i>"
    f.metadata["meta_can_be_anything"] = [42, "string", 3.14, True]

    f.hugr[f.hugr.module_root].metadata["name"] = "<i>Module Root</i>"

    b = f.inputs()[0]
    f.add_op(ops.Some(tys.Bool), b)
    f.set_outputs(b)

    validate(f.hugr, snap=snapshot)


# https://github.com/CQCL/hugr/issues/2438
def test_fndef_output_ports(snapshot):
    mod = Module()
    main = mod.define_function("main", [], [tys.Unit, tys.Unit, tys.Unit, tys.Unit])
    unit = main.add_op(ops.MakeTuple())
    main.set_outputs(*4 * [unit])

    assert mod.hugr.num_out_ports(main) == 1

    validate(mod.hugr, snap=snapshot)


def test_render_subgraph(snapshot):
    dfg = Dfg(tys.Qubit)
    (q,) = dfg.inputs()
    tagged_q = dfg.add(ops.Left(tys.Either([tys.Qubit], [tys.Qubit, INT_T]))(q))
    with dfg.add_conditional(tagged_q, dfg.load(val.TRUE)) as cond:
        with cond.add_case(0) as case0:
            q, b = case0.inputs()
            case0.set_outputs(q, b)
        with cond.add_case(1) as case1:
            q, _i, b = case1.inputs()
            case1.set_outputs(q, b)
    dfg.set_outputs(*cond[:2])
    h = dfg.hugr
    dot = h.render_dot(root=Node(10))
    assert snapshot == dot.source


def test_render_type_arg_extension_version() -> None:
    nested_type = Array(INT_T, 3)
    dfg = Dfg(nested_type)
    dfg.set_outputs(*dfg.inputs())

    dot = dfg.hugr.render_dot(
        RenderConfig(
            display_edge_extension_version=True,
            max_edge_label_length=None,
        )
    )

    assert html.escape(nested_type.render(extension_version=True)) in dot.source


def test_render_qualified_type_names() -> None:
    nested_type = Array(INT_T, 3)
    dfg = Dfg(nested_type)
    dfg.set_outputs(*dfg.inputs())

    unqualified_dot = dfg.hugr.render_dot(RenderConfig(max_edge_label_length=None))
    qualified_dot = dfg.hugr.render_dot(
        RenderConfig(
            qualify_op_name=True,
            max_edge_label_length=None,
        )
    )

    unqualified_type = html.escape(nested_type.render())
    qualified_type = html.escape(nested_type.render(qualified_name=True))
    assert f'xlabel="{unqualified_type}"' in unqualified_dot.source
    assert f'xlabel="{qualified_type}"' in qualified_dot.source


def test_render_node_type_arg_extension_version() -> None:
    """Render versions for an operation and the type nested in its arguments."""
    op_extension = ext.Extension(
        name="example.int_ops",
        version=ext.Version(0, 1, 1),
    )

    type_variable = tys.Variable(0, tys.TypeBound.Copyable)
    ieq_definition = op_extension.add_op_def(
        ext.OpDef(
            name="ieq",
            description="Equality comparison for the supplied type.",
            signature=ext.OpDefSig(
                tys.PolyFuncType(
                    params=[tys.TypeTypeParam(tys.TypeBound.Copyable)],
                    body=tys.FunctionType(
                        input=[type_variable, type_variable],
                        output=[tys.Bool],
                    ),
                )
            ),
        )
    )

    int_type = int_t(5)
    ieq = ieq_definition.instantiate(
        args=[tys.TypeTypeArg(int_type)],
        concrete_signature=tys.FunctionType(
            input=[int_type, int_type],
            output=[tys.Bool],
        ),
    )

    dfg = Dfg(int_type, int_type)
    lhs, rhs = dfg.inputs()
    result = dfg.add_op(ieq, lhs, rhs).out(0)
    dfg.set_outputs(result)

    dot = dfg.hugr.render_dot(
        RenderConfig(
            display_node_extension_version=True,
            display_edge_extension_version=True,
            max_node_label_length=None,
            max_edge_label_length=None,
        )
    )

    assert "ieq&lt;Type(int&lt;5&gt;@0.1.0)&gt;@0.1.1" in dot.source
    assert dot.source.count('xlabel="int&lt;5&gt;@0.1.0"') >= 2

    qualified_dot = dfg.hugr.render_dot(
        RenderConfig(
            qualify_op_name=True,
            display_node_extension_version=True,
            max_node_label_length=None,
        )
    )
    assert (
        "example.int_ops.ieq&lt;"
        "Type(arithmetic.int.types.int&lt;5&gt;@0.1.0)&gt;@0.1.1"
        in qualified_dot.source
    )

    unversioned_config = RenderConfig(
        max_node_label_length=None,
        max_edge_label_length=None,
    )
    assert not unversioned_config.display_node_extension_version
    assert not unversioned_config.display_edge_extension_version

    unversioned_dot = dfg.hugr.render_dot(unversioned_config)
    assert "ieq&lt;Type(int&lt;5&gt;)&gt;" in unversioned_dot.source
    assert unversioned_dot.source.count('xlabel="int&lt;5&gt;"') >= 2
    assert "@0.1.0" not in unversioned_dot.source
    assert "@0.1.1" not in unversioned_dot.source
