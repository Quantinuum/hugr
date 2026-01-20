# ruff: noqa: I001

import hugr
import hugr.ops as ops
import hugr.tys as tys
from hugr.build import Dfg
from hugr.std.collections.list import List
from hugr.std.int import INT_T, INT_TYPES_EXTENSION

from .conftest import H, QUANTUM_EXT


def test_extension_ops() -> None:
    h = Dfg(tys.Qubit)
    (q,) = h.inputs()

    h_node = h.add(H(q))
    h.set_outputs(h_node.out(0))

    op_exts = h.hugr[h_node].op.used_extensions().ids()
    assert set(op_exts) == {QUANTUM_EXT.name, "prelude"}

    exts = h.hugr.used_extensions().ids()
    assert set(exts) == {QUANTUM_EXT.name, "prelude"}


def test_core_ops() -> None:
    h = Dfg(INT_T, tys.Bool)
    a, b = h.inputs()

    tuple_n = h.add(ops.MakeTuple()(a, b))
    h.set_outputs(tuple_n.out(0))

    op_exts = h.hugr[tuple_n].op.used_extensions().ids()
    assert set(op_exts) == {INT_TYPES_EXTENSION.name, "prelude"}

    exts = h.hugr.used_extensions().ids()
    assert set(exts) == {INT_TYPES_EXTENSION.name, "prelude"}


def test_func_calls() -> None:
    h = Dfg(tys.Bool)
    [a] = h.inputs()

    f_decl = h.module_root_builder().declare_function(
        "f",
        tys.PolyFuncType(
            params=[tys.TypeTypeParam(bound=tys.TypeBound.Copyable)],
            body=tys.FunctionType([tys.Qubit], []),
        ),
    )

    call = h.call(
        f_decl,
        a,
        instantiation=tys.FunctionType([tys.Qubit], []),
        type_args=[tys.TypeTypeArg(INT_T)],
    )
    h.set_outputs()

    op_exts = h.hugr[call].op.used_extensions().ids()
    assert set(op_exts) == {INT_TYPES_EXTENSION.name, "prelude"}

    exts = h.hugr.used_extensions().ids()
    assert set(exts) == {INT_TYPES_EXTENSION.name, "prelude"}


def test_type_arguments() -> None:
    list_ty = List(tys.Qubit)
    h = Dfg(list_ty)
    (items,) = h.inputs()
    h.set_outputs(items)

    exts = h.hugr.used_extensions().ids()
    assert set(exts) == {hugr.std.collections.list.EXTENSION.name, "prelude"}
