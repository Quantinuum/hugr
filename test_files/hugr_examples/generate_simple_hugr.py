
"""A list of functions generating simple Hugr programs for testing"""

from __future__ import annotations
from curses import OK
from pathlib import Path


import hugr.ops as ops
import hugr.tys as tys
import hugr.val as val
from hugr.build.dfg import Dfg, Function
from hugr.build.function import Module
from hugr.hugr import Hugr
from hugr.std.int import INT_T, DivMod, IntVal
from hugr.std.logic import Not

vals = [val.Sum(1, tys.Sum([[INT_T], [tys.Bool, INT_T]]), [val.TRUE, IntVal(34)]), val.Tuple(val.TRUE, IntVal(23))]
direct_call = [True, False]



# FAILING hugr.ops.IncompleteOp: FuncDefn(f_name='main', inputs=[], params=[], visibility='Private')
# def test_stable_indices():
#     h = Hugr(ops.DFG([]))
#     nodes = [h.add_node(Not, num_outs=1) for _ in range(3)]
#     h.add_link(nodes[0].out(0), nodes[1].inp(0))
#     h.add_node(Not)
#     return h

# print("Saving test_stable_indices...")
# Path("test_stable_indices").with_suffix(".hugr").write_bytes(test_stable_indices().to_bytes())

# OK
def simple_id() -> Hugr:
    h = Dfg(tys.Qubit, tys.Qubit)
    a, b = h.inputs()
    h.set_outputs(a, b)
    return h.hugr
print("Saving simple_id...")
Path("simple_id").with_suffix(".hugr").write_bytes(simple_id().to_bytes())

# OK
def test_metadata() -> Hugr:
    h = Dfg(tys.Bool)
    h.metadata["name"] = "simple_id"

    (b,) = h.inputs()
    b = h.add_op(Not, b, metadata={"name": "not"})

    h.set_outputs(b)
    return h.hugr

print("Saving test_metadata...")
Path("test_metadata").with_suffix(".hugr").write_bytes(test_metadata().to_bytes())

# OK
def test_multiport() -> Hugr:
    h = Dfg(tys.Bool)
    (a,) = h.inputs()
    h.set_outputs(a, a)
    return h.hugr

print("Saving test_multiport...")
Path("test_multiport").with_suffix(".hugr").write_bytes(test_multiport().to_bytes())

# OK
def test_add_op() -> Hugr:
    h = Dfg(tys.Bool)
    (a,) = h.inputs()
    nt = h.add_op(Not, a)
    h.set_outputs(nt)

    return h.hugr

print("Saving test_add_op...")
Path("test_add_op").with_suffix(".hugr").write_bytes(test_add_op().to_bytes())

# OK
def test_tuple() -> Hugr:
    row = [tys.Bool, tys.Qubit]
    h = Dfg(*row)
    a, b = h.inputs()
    t = h.add(ops.MakeTuple()(a, b))
    a, b = h.add(ops.UnpackTuple()(t))
    h.set_outputs(a, b)

    return h.hugr

print("Saving test_tuple...")
Path("test_tuple").with_suffix(".hugr").write_bytes(test_tuple().to_bytes())

# OK
def test_multi_out() -> Hugr:
    h = Dfg(INT_T, INT_T)
    a, b = h.inputs()
    a, b = h.add(DivMod(a, b))
    h.set_outputs(a, b)
    return h.hugr

print("Saving test_multi_out...")
Path("test_multi_out").with_suffix(".hugr").write_bytes(test_multi_out().to_bytes())

# Failing hugr.ops.IncompleteOp: DFG(inputs=[])
# def test_insert():
#     h1 = Dfg(tys.Bool)
#     (a1,) = h1.inputs()
#     nt = h1.add(Not(a1))
#     h1.set_outputs(nt)

#     new_h = Hugr(ops.DFG([]))
#     h1.hugr.insert_hugr(new_h, h1.hugr.entrypoint)
#     return h1.hugr

# print("Saving test_insert...")
# Path("test_insert").with_suffix(".hugr").write_bytes(test_insert().to_bytes())

# OK
def test_insert_nested() -> Hugr:
    h1 = Dfg(tys.Bool)
    (a1,) = h1.inputs()
    nt = h1.add(Not(a1))
    h1.set_outputs(nt)

    h = Dfg(tys.Bool)
    (a,) = h.inputs()
    nested = h.insert_nested(h1, a)
    h.set_outputs(nested)
    return h.hugr

print("Saving test_insert_nested...")
Path("test_insert_nested").with_suffix(".hugr").write_bytes(test_insert_nested().to_bytes())

# OK
def test_build_nested() -> Hugr:
    h = Dfg(tys.Bool)
    (a,) = h.inputs()

    with h.add_nested(a) as nested:
        (a1,) = nested.inputs()
        nt = nested.add(Not(a1))
        nested.set_outputs(nt)

    h.set_outputs(nested)

    return h.hugr

print("Saving test_build_nested...")
Path("test_build_nested").with_suffix(".hugr").write_bytes(test_build_nested().to_bytes())

# OK
def test_build_inter_graph() -> Hugr:
    h = Dfg(tys.Bool, tys.Bool)
    (a, b) = h.inputs()
    with h.add_nested() as nested:
        nt = nested.add(Not(a))
        nested.set_outputs(nt)

    h.set_outputs(nested, b)

    return h.hugr

print("Saving test_build_inter_graph...")
Path("test_build_inter_graph").with_suffix(".hugr").write_bytes(test_build_inter_graph().to_bytes())


# Failing hugr.ops.IncompleteOp: FuncDefn(f_name='main', inputs=[Bool], params=[], visibility='Private')
# def test_ancestral_sibling():
#     h = Dfg(tys.Bool)
#     (a,) = h.inputs()
#     with h.add_nested() as nested:
#         nt = nested.add(Not(a))

#     return h.hugr

# print("Saving test_ancestral_sibling...")
# Path("test_ancestral_sibling").with_suffix(".hugr").write_bytes(test_ancestral_sibling().to_bytes())

# OK
def build_hugr_vals(val: val.Value) -> Hugr:
    d = Dfg()
    d.set_outputs(d.load(val))

    return d.hugr

for i, v in enumerate(vals):
    print(f"Saving build_hugr_vals_{i}...")
    Path(f"build_hugr_vals_{i}").with_suffix(".hugr").write_bytes(build_hugr_vals(v).to_bytes())

# OK
def test_mono_function(direct_call: bool) -> Hugr:
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
        call = f_main.call(f_id, q, instantiation=instantiation, type_args=type_args)
    else:
        load = f_main.load_function(
            f_id, instantiation=instantiation, type_args=type_args
        )
        call = f_main.add(ops.CallIndirect()(load, q))

    f_main.set_outputs(call)

    return mod.hugr

for dc in direct_call:
    print(f"Saving test_mono_function_{dc}...")
    Path(f"test_mono_function_{dc}").with_suffix(".hugr").write_bytes(test_mono_function(dc).to_bytes())

# OK
def test_literals() -> Hugr:
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

    return mod.hugr

print("Saving test_literals...")
Path("test_literals").with_suffix(".hugr").write_bytes(test_literals().to_bytes())

# OK
def test_const_type() -> None:
    mod = Module()

    mod.declare_function(
        "const_type",
        tys.PolyFuncType(
            [tys.ConstParam(tys.Qubit)],
            tys.FunctionType([], [tys.Qubit]),
        ),
    )

    return mod.hugr

print("Saving test_const_type...")
Path("test_const_type").with_suffix(".hugr").write_bytes(test_const_type().to_bytes())

# OK
def test_poly_function(direct_call: bool) -> Hugr:
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

    return mod.hugr

for dc in direct_call:
    print(f"Saving test_poly_function_{dc}...")
    Path(f"test_poly_function_{dc}").with_suffix(".hugr").write_bytes(test_poly_function(dc).to_bytes())

# OK
def test_static_output() -> Hugr:
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

    return mod.hugr

print("Saving test_static_output...")
Path("test_static_output").with_suffix(".hugr").write_bytes(test_static_output().to_bytes())

# OK
def test_function_dfg() -> Hugr:
    d = Dfg(tys.Qubit)

    f_id = d.module_root_builder().define_function("id", [tys.Qubit])
    f_id.set_outputs(f_id.input_node[0])

    (q,) = d.inputs()
    call = d.call(f_id, q)
    d.set_outputs(call)

    return d.hugr

print("Saving test_function_dfg...")
Path("test_function_dfg").with_suffix(".hugr").write_bytes(test_function_dfg().to_bytes())

# OK
def test_recursive_function() -> Hugr:
    mod = Module()

    f_recursive = mod.define_function("recurse", [tys.Qubit])
    f_recursive.declare_outputs([tys.Qubit])
    call = f_recursive.call(f_recursive, f_recursive.input_node[0])
    f_recursive.set_outputs(call)

    return mod.hugr

print("Saving test_recursive_function...")
Path("test_recursive_function").with_suffix(".hugr").write_bytes(test_recursive_function().to_bytes())

# OK
def test_state_order() -> Hugr:
    mod = Module()
    f_id = mod.define_function("id", [tys.Bool])
    f_id.set_outputs(f_id.input_node[0])

    f_main = mod.define_main([tys.Bool])
    b = f_main.input_node[0]
    call1 = f_main.call(f_id, b)
    f_main.add_state_order(call1, f_main.output_node)
    # implicit discard of bool to test state order port logic
    f_main.set_outputs()
    return mod.hugr

print("Saving test_state_order...")
Path("test_state_order").with_suffix(".hugr").write_bytes(test_state_order().to_bytes())

# OK
def test_alias() -> Hugr:
    mod = Module()
    _dfn = mod.add_alias_defn("my_int", INT_T)
    _dcl = mod.add_alias_decl("my_bool", tys.TypeBound.Copyable)

    return mod.hugr

print("Saving test_alias...")
Path("test_alias").with_suffix(".hugr").write_bytes(test_alias().to_bytes())


# OK
def test_dfg_unpack() -> Hugr:
    dfg = Dfg(tys.Tuple(tys.Bool, tys.Bool))
    bool1, _unused_bool2 = dfg.add_op(ops.UnpackTuple(), *dfg.inputs())
    cond = dfg.add_conditional(bool1)
    with cond.add_case(0) as case:
        case.set_outputs(bool1)
    with cond.add_case(1) as case:
        case.set_outputs(bool1)
    dfg.set_outputs(*cond.outputs())

    return dfg.hugr

print("Saving test_dfg_unpack...")
Path("test_dfg_unpack").with_suffix(".hugr").write_bytes(test_dfg_unpack().to_bytes())

# OK
def test_option() -> Hugr:
    dfg = Dfg(tys.Bool)
    b = dfg.inputs()[0]

    dfg.add_op(ops.Some(tys.Bool), b)

    dfg.set_outputs(b)

    return dfg.hugr

print("Saving test_option...")
Path("test_option").with_suffix(".hugr").write_bytes(test_option().to_bytes())



# OK
def test_html_labels() -> Hugr:
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

    return f.hugr

print("Saving test_html_labels...")
Path("test_html_labels").with_suffix(".hugr").write_bytes(test_html_labels().to_bytes())


# OK
def test_fndef_output_ports() -> Hugr:
    mod = Module()
    main = mod.define_function("main", [], [tys.Unit, tys.Unit, tys.Unit, tys.Unit])
    unit = main.add_op(ops.MakeTuple())
    main.set_outputs(*4 * [unit])

    return mod.hugr

print("Saving test_fndef_output_ports...")
Path("test_fndef_output_ports").with_suffix(".hugr").write_bytes(test_fndef_output_ports().to_bytes())

# OK
def test_render_subgraph() -> Hugr:
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
    return dfg.hugr

print("Saving test_render_subgraph...")
Path("test_render_subgraph").with_suffix(".hugr").write_bytes(test_render_subgraph().to_bytes())



# This is the only function that use H, I wuold omit it 
# to avoid redefining somenthing just for this one
# from .conftest import H
# 
# def simple_fn() -> Hugr:
#     f = Function("prepare_qubit", [tys.Bool, tys.Qubit])
#     [b, q] = f.inputs()

#     h = f.add_op(H, q)
#     q = h.out(0)

#     not_node = f.add_op(Not, b)

#     f.set_outputs(q, not_node, b)
#     return f.hugr

# Path("simple_fn").with_suffix(".hugr").write_bytes(simple_fn().to_bytes())
