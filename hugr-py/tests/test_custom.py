from dataclasses import dataclass

import pytest

from hugr import ext, model, ops, tys
from hugr.build.dfg import Dfg
from hugr.ext import UsedExtensionResolver
from hugr.hugr import Hugr, Node
from hugr.ops import AsExtOp, Custom, ExtOp
from hugr.package import Package
from hugr.std.float import FLOAT_T
from hugr.std.float import FLOAT_TYPES_EXTENSION as FLOAT_EXT
from hugr.std.int import INT_OPS_EXTENSION, INT_TYPES_EXTENSION, DivMod, int_t
from hugr.std.logic import EXTENSION as LOGIC_EXT
from hugr.std.logic import Not

from .conftest import CX, QUANTUM_EXT, H, Measure, Rz, validate

STRINGLY_EXT = ext.Extension("my_extension", ext.Version(0, 0, 0))
_STRINGLY_DEF = STRINGLY_EXT.add_op_def(
    ext.OpDef(
        "StringlyOp",
        signature=ext.OpDefSig(
            tys.PolyFuncType([tys.StringParam()], tys.FunctionType.endo([]))
        ),
    )
)


@dataclass
class StringlyOp(AsExtOp):
    tag: str

    def op_def(self) -> ext.OpDef:
        return STRINGLY_EXT.get_op("StringlyOp")

    def type_args(self) -> list[tys.TypeArg]:
        return [tys.StringArg(self.tag)]

    def cached_signature(self) -> tys.FunctionType | None:
        return tys.FunctionType.endo([])

    @classmethod
    def from_ext(cls, custom: ops.ExtOp) -> "StringlyOp":
        match custom:
            case ops.ExtOp(
                _op_def=_STRINGLY_DEF,
                args=[tys.StringArg(tag)],
            ):
                return cls(tag=tag)
            case _:
                msg = f"Invalid custom op: {custom}"
                raise AsExtOp.InvalidExtOp(msg)


def test_stringly_typed():
    dfg = Dfg()
    n = dfg.add(StringlyOp("world")())
    dfg.set_outputs()
    assert dfg.hugr[n].op == StringlyOp("world")
    validate(Package([dfg.hugr], [STRINGLY_EXT]))

    new_h = Hugr._from_serial(dfg.hugr._to_serial())

    assert isinstance(new_h[n].op, Custom)

    # Resolve with the extension in the registry
    registry = ext.ExtensionRegistry()
    registry.register(STRINGLY_EXT)
    new_h.resolve_extensions(registry)

    assert isinstance(new_h[n].op, ExtOp)


def test_registry():
    reg = ext.ExtensionRegistry()
    reg.register(LOGIC_EXT)
    assert reg.get_extension(LOGIC_EXT.name).name == LOGIC_EXT.name
    assert len(reg.versioned_extensions) == 1

    with pytest.raises(ext.ExtensionRegistry.ExtensionNotFound):
        reg.get_extension("not_found")


@pytest.fixture
def registry() -> ext.ExtensionRegistry:
    reg = ext.ExtensionRegistry()
    reg.register(LOGIC_EXT)
    reg.register(QUANTUM_EXT)
    reg.register(STRINGLY_EXT)
    reg.register(INT_TYPES_EXTENSION)
    reg.register(INT_OPS_EXTENSION)
    reg.register(FLOAT_EXT)

    return reg


@pytest.mark.parametrize(
    "as_ext",
    [Not, DivMod, H, CX, Measure, Rz, StringlyOp("hello")],
)
def test_custom_op(as_ext: AsExtOp, registry: ext.ExtensionRegistry):
    ext_op = as_ext.ext_op

    assert ExtOp.from_ext(ext_op) == ext_op

    assert type(as_ext).from_ext(ext_op) == as_ext
    custom = as_ext._to_serial(Node(0)).deserialize()
    assert isinstance(custom, Custom)
    assert custom.extension_version == ext_op.op_def().get_extension().version
    # ExtOp compared to Custom via `to_custom`
    assert custom.resolve(registry) == ext_op
    assert ext_op == as_ext
    assert as_ext == ext_op


def test_custom_bad_eq():
    assert Not != DivMod

    bad_custom_sig = Custom("Not", extension=LOGIC_EXT.name)  # empty signature

    assert Not != bad_custom_sig

    bad_custom_args = Custom(
        "Not",
        extension=LOGIC_EXT.name,
        signature=tys.FunctionType.endo([tys.Bool]),
        args=[tys.Bool.type_arg()],
    )

    assert Not != bad_custom_args


_LIST_T = STRINGLY_EXT.add_type_def(
    ext.TypeDef(
        "List",
        description="A list of elements.",
        params=[tys.TypeTypeParam(tys.TypeBound.Linear)],
        bound=ext.FromParamsBound([0]),
    )
)

_BOOL_LIST_T = _LIST_T.instantiate([tys.Bool.type_arg()])


@pytest.mark.parametrize(
    "ext_t",
    [FLOAT_T, int_t(5), _BOOL_LIST_T],
)
def test_custom_type(ext_t: tys.ExtType, registry: ext.ExtensionRegistry):
    opaque = ext_t._to_serial().deserialize()
    assert isinstance(opaque, tys.Opaque)
    assert opaque.extension_version == ext_t.type_def.get_extension().version
    resolved = opaque._resolve_used_extensions(UsedExtensionResolver(), registry)
    assert resolved == ext_t

    resolved = opaque._resolve_used_extensions(
        UsedExtensionResolver(), ext.ExtensionRegistry()
    )
    assert resolved == opaque

    f_t = tys.FunctionType.endo([ext_t])
    f_t_opaque = f_t._to_serial().deserialize()
    assert isinstance(f_t_opaque.input[0], tys.Opaque)

    resolved = f_t_opaque._resolve_used_extensions(UsedExtensionResolver(), registry)
    assert resolved == f_t


def test_qualified_name():
    # Test TypeDef with extension
    assert _LIST_T.qualified_name() == "my_extension.List"

    # Test TypeDef without extension
    standalone_type = ext.TypeDef(
        "Standalone",
        description="A standalone type.",
        params=[],
        bound=ext.ExplicitBound(tys.TypeBound.Copyable),
    )
    assert standalone_type.qualified_name() == "Standalone"

    # Test OpDef with extension
    assert _STRINGLY_DEF.qualified_name() == "my_extension.StringlyOp"


def _versioned_ext(version: ext.Version) -> ext.Extension:
    """Helper function to create an extension with a given version for testing."""
    extension = ext.Extension("versioned_ext", version)
    extension.add_op_def(ext.OpDef("my_op", ext.OpDefSig(tys.FunctionType.endo([]))))
    extension.add_type_def(
        ext.TypeDef(
            "MyType",
            "A versioned type.",
            [],
            ext.ExplicitBound(tys.TypeBound.Copyable),
        )
    )
    return extension


def test_registry_version_resolution():
    """Test that registry resolution picks the highest compatible version of an
    extension."""

    ext_0_2_5 = _versioned_ext(ext.Version(0, 2, 5))
    ext_0_3_0 = _versioned_ext(ext.Version(0, 3, 0))
    ext_1_3_0 = _versioned_ext(ext.Version(1, 3, 0))
    reg = ext.ExtensionRegistry()
    reg.register(ext_0_2_5)
    reg.register(ext_0_3_0)
    reg.register(ext_1_3_0)

    assert reg.get_extension("versioned_ext", ext.Version(0, 2, 3)) is ext_0_2_5
    assert reg.get_extension("versioned_ext", ext.Version(0, 3, 0)) is ext_0_3_0
    assert reg.get_extension("versioned_ext", ext.Version(1, 2, 3)) is ext_1_3_0

    custom = ops.Custom(
        "my_op",
        tys.FunctionType.endo([]),
        "versioned_ext",
        extension_version=ext.Version(0, 2, 3),
    )
    resolved = custom.resolve(reg)
    assert isinstance(resolved, ops.ExtOp)
    assert resolved.op_def().get_extension() is ext_0_2_5

    opaque = tys.Opaque(
        "MyType",
        tys.TypeBound.Copyable,
        extension="versioned_ext",
        extension_version=ext.Version(0, 2, 3),
    )
    resolved_ty = opaque._resolve_used_extensions(UsedExtensionResolver(), reg)
    assert isinstance(resolved_ty, tys.ExtType)
    assert resolved_ty.type_def.get_extension() is ext_0_2_5


def test_model_versions():
    """Model import/export keeps extension versions on custom ops and types."""

    version = ext.Version(0, 2, 3)
    opaque = tys.Opaque(
        "MyType",
        tys.TypeBound.Copyable,
        extension="versioned_ext",
        extension_version=version,
    )
    signature = tys.FunctionType(input=[], output=[opaque])
    dfg = Dfg()
    [out] = dfg.add(
        ops.Custom(
            "my_op",
            signature=signature,
            extension="versioned_ext",
            extension_version=version,
        )()
    )
    dfg.set_outputs(out)

    model_pkg = Package([dfg.hugr]).to_model()
    assert "versioned_ext.my_op@0.2.3" in str(model_pkg)
    assert "versioned_ext.MyType@0.2.3" in str(model_pkg)

    [hugr] = Package.from_model(model_pkg).modules
    custom = next(
        data.op for _, data in hugr.nodes() if isinstance(data.op, ops.Custom)
    )

    assert custom.extension_version == version
    [output] = custom.signature.output
    assert isinstance(output, tys.Opaque)
    assert output.extension_version == version


@pytest.mark.parametrize(
    ("imports", "resolve_from", "expected"),
    [
        (
            "(import versioned_ext.my_op@0.2.3)\n"
            "(import versioned_ext.MyType@0.2.3)",
            None,
            "0.2.3",
        ),
        (
            """
            (import versioned_ext.my_op@0.2.3)
            (import versioned_ext.my_op@0.3.0)
            (import versioned_ext.MyType@0.2.3)
            (import versioned_ext.MyType@0.3.0)
            """,
            None,
            "0.3.0",
        ),
        (
            "(import versioned_ext.my_op)\n(import versioned_ext.MyType)",
            None,
            None,
        ),
        (
            "(import versioned_ext.my_op)\n(import versioned_ext.MyType)",
            ext.Version(0, 3, 0),
            "0.3.0",
        ),
        (
            """
            (import versioned_ext.my_op)
            (import versioned_ext.my_op@0.2.3)
            (import versioned_ext.MyType)
            (import versioned_ext.MyType@0.2.3)
            """,
            None,
            None,
        ),
        (
            """
            (import versioned_ext.my_op)
            (import versioned_ext.my_op@0.2.3)
            (import versioned_ext.MyType)
            (import versioned_ext.MyType@0.2.3)
            """,
            ext.Version(0, 3, 0),
            "0.3.0",
        ),
    ],
)
def test_model_import_versions_from_imports(
    imports: str, resolve_from: ext.Version | None, expected: str | None
):
    """Unversioned model uses explicit versions before registry fallback."""
    registry = None
    if resolve_from is not None:
        registry = ext.ExtensionRegistry()
        registry.register(_versioned_ext(resolve_from))

    expected_version = ext.Version.parse(expected) if expected is not None else None

    source = f"""
        (hugr 0)

        (mod)

        {imports}

        (define-func public main (core.fn [] [versioned_ext.MyType])
          (dfg [] [%0]
            (signature (core.fn [] [versioned_ext.MyType]))
            ((versioned_ext.my_op) [] [%0]
                  (signature (core.fn [] [versioned_ext.MyType])))))
    """

    [hugr] = Package.from_model(
        model.Package.from_str(source.strip()), resolve_from=registry
    ).modules
    custom = next(
        data.op
        for _, data in hugr.nodes()
        if isinstance(data.op, ops.Custom | ops.ExtOp)
    )

    if isinstance(custom, ops.Custom):
        assert custom.extension_version == expected_version
    else:
        assert custom.op_def().get_extension().version == expected_version
    assert custom.signature is not None
    [output] = custom.signature.output
    match output:
        case tys.Opaque(extension_version=extension_version):
            assert extension_version == expected_version
        case tys.ExtType(type_def=type_def):
            assert type_def.get_extension().version == expected_version
        case _:
            msg = f"unexpected output type: {output}"
            raise AssertionError(msg)
