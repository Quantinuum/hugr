
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

FILE_PREFIX = "NCL_"

direct_call = [True, False]

#########################
# included in simple_hugr
########################
def test_metadata() -> Hugr:
    h = Dfg(tys.Bool)
    h.metadata["name"] = "simple_id"

    (b,) = h.inputs()
    b = h.add_op(Not, b, metadata={"name": "not"})

    h.set_outputs(b)
    return h.hugr


def test_multi_out() -> Hugr:
    h = Dfg(INT_T, INT_T)
    a, b = h.inputs()
    a, b = h.add(DivMod(a, b))
    h.set_outputs(a, b)
    return h.hugr

def test_add_op() -> Hugr:
    h = Dfg(tys.Bool)
    (a,) = h.inputs()
    nt = h.add_op(Not, a)
    h.set_outputs(nt)

    return h.hugr

def build_hugr_vals(val: val.Value) -> Hugr:
    d = Dfg()
    d.set_outputs(d.load(val))

    return d.hugr

def test_multiport() -> Hugr:
    h = Dfg(tys.Bool)
    (a,) = h.inputs()
    h.set_outputs(a, a)
    return h.hugr
###################################################

def simple_hugr() -> Hugr:
    d = Dfg(tys.Qubit, tys.Bool, INT_T, INT_T)
    d.metadata["name"] = "simple_hugr"
    q, b, i1, i2 = d.inputs()
    
    b = d.add_op(Not, b, metadata={"name": "not"})
    c = d.add_op(Not, d.load(val.TRUE), metadata={"name": "not_true"})
    i1, i2 = d.add(DivMod(i1, i2))
    d.set_outputs(q, b, b, c, i1, i2)
    
    return d.hugr

print("Saving simple_hugr...")
Path(f"{FILE_PREFIX}simple_hugr").with_suffix(".hugr").write_bytes(simple_hugr().to_bytes())


def hugr_nested() -> Hugr:
    h = Dfg(tys.Bool)
    (a,) = h.inputs()

    with h.add_nested(a) as nested:
        (a1,) = nested.inputs()
        nt = nested.add(Not(a1))
        nested.set_outputs(nt)

    h.set_outputs(nested)

    return h.hugr

print("Saving hugr_nested...")
Path(f"{FILE_PREFIX}hugr_nested").with_suffix(".hugr").write_bytes(hugr_nested().to_bytes())


def hugr_nested_w_external_edge() -> Hugr:
    h = Dfg(tys.Bool, tys.Bool)
    (a, b) = h.inputs()
    with h.add_nested() as nested:
        nt = nested.add(Not(a=a))
        nested.set_outputs(nt)

    h.set_outputs(nested, b)

    return h.hugr

print("Saving hugr_nested_w_external_edge...")
Path(f"{FILE_PREFIX}hugr_nested_w_external_edge").with_suffix(".hugr").write_bytes(hugr_nested_w_external_edge().to_bytes())


def hugr_w_function_call(direct_call: bool) -> Hugr:
    mod = Module()

    f_id = mod.declare_function(
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

    f_main = mod.define_main([tys.Qubit])
    q = f_main.inputs()[0]
    # for now concrete instantiations have to be provided.
    instantiation = tys.FunctionType.endo([tys.Qubit])
    type_args=[
            tys.StringArg("string"),
            tys.BoundedNatArg(42),
            tys.BytesArg(b"HUGR"),
            tys.FloatArg(0.9),
        ]
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
    print(f"Saving hugr_w_function_call_{dc}...")
    Path(f"{FILE_PREFIX}hugr_w_function_{"direct" if dc else "indirect"}_call").with_suffix(".hugr").write_bytes(hugr_w_function_call(dc).to_bytes())


def hugr_w_recursive_function() -> Hugr:
    mod = Module()

    f_recursive = mod.define_function("recurse", [tys.Qubit])
    f_recursive.declare_outputs([tys.Qubit])
    call = f_recursive.call(f_recursive, f_recursive.input_node[0])
    f_recursive.set_outputs(call)

    return mod.hugr

print("Saving hugr_w_recursive_function...")
Path(f"{FILE_PREFIX}hugr_w_recursive_function").with_suffix(".hugr").write_bytes(hugr_w_recursive_function().to_bytes())




def hugr_conditional() -> Hugr:
    dfg = Dfg(tys.Tuple(tys.Bool, tys.Bool))
    bool1, _ = dfg.add_op(ops.UnpackTuple(), *dfg.inputs())
    cond = dfg.add_conditional(bool1)
    with cond.add_case(0) as case:
        case.set_outputs(bool1)
    with cond.add_case(1) as case:
        case.set_outputs(bool1)
    dfg.set_outputs(*cond.outputs())

    return dfg.hugr

print("Saving hugr_conditional...")
Path(f"{FILE_PREFIX}hugr_conditional").with_suffix(".hugr").write_bytes(hugr_conditional().to_bytes())


