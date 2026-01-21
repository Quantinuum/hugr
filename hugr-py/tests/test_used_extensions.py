# ruff: noqa: I001

import hugr
import hugr.ops as ops
import hugr.tys as tys
from hugr import ext

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


def test_op_signature_contains_same_extension() -> None:
    """Test that used_extensions() works when an op's signature contains
    types from the same extension as the operation itself.

    Regression test for https://github.com/Quantinuum/hugr/issues/2829
    """

    # Create an extension with a custom type
    my_ext = ext.Extension("test.self_referential", ext.Version(0, 1, 0))
    my_type_def = my_ext.add_type_def(
        ext.TypeDef(
            name="MyType",
            description="A custom type",
            params=[],
            bound=ext.ExplicitBound(tys.TypeBound.Copyable),
        )
    )

    # Create an ExtType from this extension's type definition
    my_type = tys.ExtType(my_type_def, args=[])

    # Add an operation to the same extension that uses MyType in its signature
    my_ext.add_op_def(
        ext.OpDef(
            name="ProcessMyType",
            description="An operation that uses MyType",
            signature=ext.OpDefSig(tys.FunctionType([my_type], [my_type])),
        )
    )

    # Create an ExtOp from this definition
    op = ops.ExtOp(my_ext.get_op("ProcessMyType"), args=[])

    # This would have failed with ExtensionRegistry.ExtensionExists before the fix
    # because the signature contains my_type (from my_ext) and we also add my_ext
    exts = op.used_extensions()
    assert my_ext.name in exts.ids()
