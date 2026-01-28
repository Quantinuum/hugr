# ruff: noqa: I001

import hugr
import hugr.ops as ops
import hugr.tys as tys
from hugr import ext, val

from hugr.build import Dfg
from hugr.std.collections.list import List
from hugr.std.int import INT_T, INT_TYPES_EXTENSION
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


@pytest.mark.parametrize(
    ("typ", "extensions"),
    [
        # Opaque type
        (TEST_TYPE_OPAQUE, [TEST_EXT]),
        (tys.Sum([[TEST_TYPE_OPAQUE], [tys.Bool]]), [TEST_EXT]),
        (tys.Tuple(TEST_TYPE_OPAQUE, tys.Bool), [TEST_EXT]),
        (tys.Option(TEST_TYPE_OPAQUE), [TEST_EXT]),
        (tys.Either([TEST_TYPE_OPAQUE], [tys.Bool]), [TEST_EXT]),
        (tys.UnitSum(3), []),
        (tys.FunctionType([TEST_TYPE_OPAQUE], [tys.Bool]), [TEST_EXT]),
        (
            tys.PolyFuncType(
                [tys.FloatParam()], tys.FunctionType([TEST_TYPE_OPAQUE], [tys.Bool])
            ),
            [TEST_EXT],
        ),
        (tys.Variable(0, tys.TypeBound.Copyable), []),
        (tys.RowVariable(0, tys.TypeBound.Copyable), []),
        (tys.Alias("MyAlias", tys.TypeBound.Copyable), []),
    ],
)
def test_type_resolution(typ: tys.Type, extensions: list[ext.Extension]) -> None:
    """Test that Opaque types are tracked and resolved correctly."""
    _, result = typ._resolve_used_extensions()
    for extension in extensions:
        assert extension.name in result.unresolved_extensions
    if extensions:
        assert (TEST_EXT.name, "TestType") in result.unresolved_types
    assert not result.unresolved_ops

    test_registry = ext.ExtensionRegistry()
    for extension in extensions:
        test_registry.add_extension(extension)
    _, result = typ._resolve_used_extensions(test_registry)
    for extension in extensions:
        assert extension.name in result.used_extensions.ids()
    assert not result.unresolved_types
    assert not result.unresolved_ops


@pytest.mark.parametrize(
    ("arg", "extensions"),
    [
        (tys.TypeTypeArg(TEST_TYPE_OPAQUE), [TEST_EXT]),
        (tys.ListArg([tys.TypeTypeArg(TEST_TYPE_OPAQUE)]), [TEST_EXT]),
        (
            tys.TupleArg([tys.TypeTypeArg(TEST_TYPE_OPAQUE), tys.BoundedNatArg(5)]),
            [TEST_EXT],
        ),
        (
            tys.ListConcatArg([tys.ListArg([tys.TypeTypeArg(TEST_TYPE_OPAQUE)])]),
            [TEST_EXT],
        ),
        (
            tys.TupleConcatArg([tys.TupleArg([tys.TypeTypeArg(TEST_TYPE_OPAQUE)])]),
            [TEST_EXT],
        ),
        (tys.VariableArg(0, tys.ConstParam(TEST_TYPE_OPAQUE)), [TEST_EXT]),
        (tys.BoundedNatArg(42), []),
        (tys.StringArg("hello"), []),
        (tys.FloatArg(3.14), []),
        (tys.BytesArg(b"bytes"), []),
    ],
)
def test_type_arg_resolution(arg: tys.TypeArg, extensions: list[ext.Extension]) -> None:
    """Test that type arguments are tracked and resolved correctly."""
    _, result = arg._resolve_used_extensions()
    for extension in extensions:
        assert extension.name in result.unresolved_extensions
    if extensions:
        assert (TEST_EXT.name, "TestType") in result.unresolved_types
    assert not result.unresolved_ops

    test_registry = ext.ExtensionRegistry()
    for extension in extensions:
        test_registry.add_extension(extension)
    _, result = arg._resolve_used_extensions(test_registry)
    for extension in extensions:
        assert extension.name in result.used_extensions.ids()
    assert not result.unresolved_types
    assert not result.unresolved_ops


@pytest.mark.parametrize(
    ("param", "extensions"),
    [
        (tys.ListParam(tys.ConstParam(TEST_TYPE_OPAQUE)), [TEST_EXT]),
        (
            tys.TupleParam([tys.ConstParam(TEST_TYPE_OPAQUE), tys.BoundedNatParam()]),
            [TEST_EXT],
        ),
        (tys.ConstParam(TEST_TYPE_OPAQUE), [TEST_EXT]),
        (tys.TypeTypeParam(tys.TypeBound.Copyable), []),
        (tys.BoundedNatParam(100), []),
        (tys.StringParam(), []),
        (tys.FloatParam(), []),
        (tys.BytesParam(), []),
    ],
)
def test_type_param_resolution(
    param: tys.TypeParam, extensions: list[ext.Extension]
) -> None:
    """Test that type parameters are tracked and resolved correctly."""
    _, result = param._resolve_used_extensions()
    for extension in extensions:
        assert extension.name in result.unresolved_extensions
    if extensions:
        assert (TEST_EXT.name, "TestType") in result.unresolved_types
    assert not result.unresolved_ops

    test_registry = ext.ExtensionRegistry()
    for extension in extensions:
        test_registry.add_extension(extension)
    _, result = param._resolve_used_extensions(test_registry)
    for extension in extensions:
        assert extension.name in result.used_extensions.ids()
    assert not result.unresolved_types
    assert not result.unresolved_ops


@pytest.mark.parametrize(
    ("op", "extensions"),
    [
        (TEST_OP_OPAQUE, [TEST_EXT]),
        (ops.MakeTuple([TEST_TYPE_OPAQUE]), [TEST_EXT]),
        (ops.UnpackTuple([TEST_TYPE_OPAQUE]), [TEST_EXT]),
        (ops.Tag(0, tys.Sum([[TEST_TYPE_OPAQUE], []])), [TEST_EXT]),
        (ops.LoadConst(TEST_TYPE_OPAQUE), [TEST_EXT]),
        (ops.Conditional(tys.Sum([[TEST_TYPE_OPAQUE], []]), [tys.Bool]), [TEST_EXT]),
        (ops.Case([TEST_TYPE_OPAQUE]), [TEST_EXT]),
        (ops.TailLoop([TEST_TYPE_OPAQUE], [tys.Bool]), [TEST_EXT]),
        (ops.DFG([TEST_TYPE_OPAQUE]), [TEST_EXT]),
        (ops.CFG([TEST_TYPE_OPAQUE]), [TEST_EXT]),
        (ops.DataflowBlock([TEST_TYPE_OPAQUE]), [TEST_EXT]),
        (ops.ExitBlock([TEST_TYPE_OPAQUE]), [TEST_EXT]),
        (ops.FuncDefn("test_fn", [TEST_TYPE_OPAQUE]), [TEST_EXT]),
        (
            ops.FuncDecl(
                "test_fn",
                tys.PolyFuncType([], tys.FunctionType([TEST_TYPE_OPAQUE], [])),
            ),
            [TEST_EXT],
        ),
        (ops.CallIndirect(tys.FunctionType([TEST_TYPE_OPAQUE], [])), [TEST_EXT]),
        (ops.AliasDefn("MyAlias", TEST_TYPE_OPAQUE), [TEST_EXT]),
    ],
)
def test_op_resolution(op: ops.Op, extensions: list[ext.Extension]) -> None:
    """Test that ops are tracked and resolved correctly."""
    _, result = op._resolve_used_extensions()
    for extension in extensions:
        assert extension.name in result.unresolved_extensions

    if isinstance(op, ops.Custom):
        assert (op.extension, op.op_name) in result.unresolved_ops
        assert not result.unresolved_types
    elif extensions:
        assert not result.unresolved_ops
        assert (TEST_EXT.name, "TestType") in result.unresolved_types
    else:
        assert not result.unresolved_ops
        assert not result.unresolved_types

    test_ext_registry = ext.ExtensionRegistry()
    for extension in extensions:
        test_ext_registry.add_extension(extension)
    _, result = op._resolve_used_extensions(test_ext_registry)
    for extension in extensions:
        assert extension.name in result.used_extensions.ids()
    assert not result.unresolved_ops
    assert not result.unresolved_types


@pytest.mark.parametrize(
    ("value", "extensions"),
    [
        (val.Sum(0, tys.Sum([[TEST_TYPE_OPAQUE], []]), []), [TEST_EXT]),
        (val.Tuple(val.TRUE), []),
        (val.Some(val.TRUE), []),
        (val.None_(TEST_TYPE_OPAQUE), [TEST_EXT]),
        (val.Left([], [TEST_TYPE_OPAQUE]), [TEST_EXT]),
        (val.Right([TEST_TYPE_OPAQUE], []), [TEST_EXT]),
        (val.UnitSum(0, 3), []),
        (val.Extension("test", TEST_TYPE_OPAQUE, {}), [TEST_EXT]),
    ],
)
def test_value_resolution(value: val.Value, extensions: list[ext.Extension]) -> None:
    """Test that values are tracked and resolved correctly."""
    result = value._resolve_used_extensions_inplace()
    for extension in extensions:
        assert extension.name in result.unresolved_extensions

    # Reset the value for the second test by creating a fresh copy
    test_ext_registry = ext.ExtensionRegistry()
    for extension in extensions:
        test_ext_registry.add_extension(extension)
    result = value._resolve_used_extensions_inplace(test_ext_registry)
    for extension in extensions:
        assert extension.name in result.used_extensions.ids()


def test_hugr_with_opaque_type_resolve() -> None:
    """Test that Hugr.used_extensions can resolve opaque types."""
    # Create a DFG with the opaque type
    h = Dfg(TEST_TYPE_OPAQUE)
    (inp,) = h.inputs()
    h.set_outputs(inp)

    # Without resolve_from, unresolved extensions are tracked
    result_no_resolve = h.hugr.used_extensions()
    assert TEST_EXT.name in result_no_resolve.unresolved_extensions

    # With resolve_from, should work
    test_ext_registry = ext.ExtensionRegistry()
    test_ext_registry.add_extension(TEST_EXT)
    exts = h.hugr.used_extensions(resolve_from=test_ext_registry)
    assert TEST_EXT.name in exts.used_extensions.ids()
