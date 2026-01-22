# ruff: noqa: I001

import hugr
import hugr.ops as ops
import hugr.tys as tys
from hugr import ext

from hugr.build import Dfg
from hugr.std.collections.list import List
from hugr.std.int import INT_T, INT_TYPES_EXTENSION
from hugr.utils import UnresolvedExtensionError
import pytest

from .conftest import H, QUANTUM_EXT, TEST_EXT, TEST_TYPE_OPAQUE, TEST_OP_OPAQUE


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


def test_opaque_type_without_resolve() -> None:
    """Test that Opaque types raise UnresolvedExtensionError without resolve_from."""
    with pytest.raises(UnresolvedExtensionError):
        TEST_TYPE_OPAQUE.used_extensions()


def test_opaque_type_with_resolve(test_ext_registry: ext.ExtensionRegistry) -> None:
    """Test that Opaque types can be resolved with resolve_from."""
    exts = TEST_TYPE_OPAQUE.used_extensions(resolve_from=test_ext_registry)
    assert TEST_EXT.name in exts.ids()


def test_custom_op_without_resolve() -> None:
    """Test that Custom ops raise UnresolvedExtensionError without resolve_from."""
    with pytest.raises(UnresolvedExtensionError):
        TEST_OP_OPAQUE.used_extensions()


def test_custom_op_with_resolve(test_ext_registry: ext.ExtensionRegistry) -> None:
    """Test that Custom operations can be resolved with resolve_from."""
    exts = TEST_OP_OPAQUE.used_extensions(resolve_from=test_ext_registry)
    assert TEST_EXT.name in exts.ids()


def test_hugr_with_opaque_type_resolve(
    test_ext_registry: ext.ExtensionRegistry,
) -> None:
    """Test that Hugr.used_extensions can resolve opaque types."""
    # Create a DFG with the opaque type
    h = Dfg(TEST_TYPE_OPAQUE)
    (inp,) = h.inputs()
    h.set_outputs(inp)

    # Without resolve_from, this should raise
    with pytest.raises(UnresolvedExtensionError):
        h.hugr.used_extensions()

    # With resolve_from, should work
    exts = h.hugr.used_extensions(resolve_from=test_ext_registry)
    assert TEST_EXT.name in exts.ids()


def test_nested_opaque_type_resolve(test_ext_registry: ext.ExtensionRegistry) -> None:
    """Test resolution of opaque types nested in Sum types."""
    # Create a Sum type with the opaque type
    sum_ty = tys.Sum([[TEST_TYPE_OPAQUE], [tys.Bool]])

    # Without resolve_from, this should raise
    with pytest.raises(UnresolvedExtensionError):
        sum_ty.used_extensions()

    # With resolve_from, should work
    exts = sum_ty.used_extensions(resolve_from=test_ext_registry)
    assert TEST_EXT.name in exts.ids()
