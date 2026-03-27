import pytest

from hugr import Hugr, ext, tys
from hugr._hugr.linking import HugrLinkingError, link_modules
from hugr.build import Module
from hugr.ops import FuncDefn
from hugr.package import Package
from hugr.std import float, int, logic, ptr


def build_module(*, entrypoint: bool, public_func: bool = False) -> Hugr:
    builder = Module()
    if entrypoint:
        main = builder.define_function(
            "main", input_types=[tys.Bool], output_types=[tys.Bool], visibility="Public"
        )
        main.set_outputs(*main.inputs())
        builder.hugr.entrypoint = main.parent_node
    elif public_func:
        # Entrypoint is already public, so we only need to add one
        # if no entrypoint was generated.
        func = builder.define_function(
            "public_func",
            input_types=[tys.Bool],
            output_types=[tys.Bool],
            visibility="Public",
        )
        func.set_outputs(*func.inputs())

    return builder.hugr


def test_link_modules_no_entrypoints():
    hugr1 = build_module(entrypoint=False)
    hugr2 = build_module(entrypoint=False)

    linked = Hugr.from_bytes(link_modules(hugr1.to_bytes(), hugr2.to_bytes()))
    assert linked.entrypoint == linked.module_root


def test_link_modules_entrypoint_lhs():
    hugr1 = build_module(entrypoint=True)
    hugr2 = build_module(entrypoint=False)

    linked = Hugr.from_bytes(link_modules(hugr1.to_bytes(), hugr2.to_bytes()))
    assert linked.entrypoint != linked.module_root
    entrypoint = linked.entrypoint_op()
    assert isinstance(entrypoint, FuncDefn)
    assert entrypoint.f_name == "main"


def test_link_modules_entrypoint_rhs():
    hugr1 = build_module(entrypoint=False)
    hugr2 = build_module(entrypoint=True)

    linked = Hugr.from_bytes(link_modules(hugr1.to_bytes(), hugr2.to_bytes()))
    assert linked.entrypoint != linked.module_root
    entrypoint = linked.entrypoint_op()
    assert isinstance(entrypoint, FuncDefn)
    assert entrypoint.f_name == "main"


def test_link_modules_multiple_entrypoints():
    hugr1 = build_module(entrypoint=True)
    hugr2 = build_module(entrypoint=True)

    with pytest.raises(ValueError, match="Cannot link two executable modules together"):
        link_modules(hugr1.to_bytes(), hugr2.to_bytes())


def test_link_modules_linking_error():
    hugr1 = build_module(entrypoint=False, public_func=True)
    hugr2 = build_module(entrypoint=False, public_func=True)

    with pytest.raises(
        HugrLinkingError,
        match=r"Source \(Node\([0-9]+\)\) and target \(Node\([0-9]+\)\) both contained FuncDefn with same public name public_func",  # noqa: E501
    ):
        link_modules(hugr1.to_bytes(), hugr2.to_bytes())


def test_link_packages_no_modules():
    pkg1 = Package(modules=[])
    pkg2 = Package(modules=[])

    result_pkg = pkg1.link(pkg2)

    assert result_pkg.modules == []


def test_link_packages_extensions():
    pkg1 = Package(
        modules=[build_module(entrypoint=False)],
        extensions=[
            int.CONVERSIONS_EXTENSION,
            int.INT_TYPES_EXTENSION,
            int.INT_OPS_EXTENSION,
            # Shared
            logic.EXTENSION,
            ptr.EXTENSION,
        ],
    )
    pkg2 = Package(
        modules=[build_module(entrypoint=False)],
        extensions=[
            float.FLOAT_OPS_EXTENSION,
            float.FLOAT_TYPES_EXTENSION,
            # Shared
            logic.EXTENSION,
            ptr.EXTENSION,
        ],
    )

    result_pkg = pkg1.link(pkg2)

    assert result_pkg.extensions == [
        int.CONVERSIONS_EXTENSION,
        int.INT_TYPES_EXTENSION,
        int.INT_OPS_EXTENSION,
        logic.EXTENSION,
        ptr.EXTENSION,
        float.FLOAT_OPS_EXTENSION,
        float.FLOAT_TYPES_EXTENSION,
    ]


def test_link_packages_extension_requires_resolution():
    """Tests that a package using an extension can be serialized and deserialized during
    the linking process."""
    type_def = ext.TypeDef(
        name="TestType",
        description="A type definition.",
        params=[],
        bound=ext.ExplicitBound(tys.TypeBound.Copyable),
    )
    extension = ext.Extension(
        version=ext.Version(0, 1, 0),
        name="outer",
        types={},
    )
    extension.add_type_def(type_def)
    opaque_type_def = tys.Opaque(
        id="TestType", bound=tys.TypeBound.Copyable, extension=extension.name
    )

    # Build a HUGR with the custom opaque type that requires the extension to be
    # resolved during the deserialization process that happens during linking.
    builder = Module()
    func = builder.define_function(
        "use_type_def",
        input_types=[opaque_type_def],
        output_types=[opaque_type_def],
    )
    func.set_outputs(*func.inputs())

    pkg1 = Package(modules=[builder.hugr], extensions=[extension])
    pkg2 = Package(modules=[build_module(entrypoint=False)])

    result_pkg = pkg1.link(pkg2)

    assert result_pkg.extensions == [extension]
