import pytest

from hugr import Hugr, tys
from hugr._hugr.linking import link_modules
from hugr.build import Module
from hugr.ops import FuncDefn


def build_module(*, entrypoint: bool) -> Hugr:
    builder = Module()
    if entrypoint:
        main = builder.define_function(
            "main", input_types=[tys.Bool], output_types=[tys.Bool], visibility="Public"
        )
        main.set_outputs(*main.inputs())
        builder.hugr.entrypoint = main.parent_node

    return builder.hugr


def test_no_entrypoints():
    hugr1 = build_module(entrypoint=False)
    hugr2 = build_module(entrypoint=False)

    linked = Hugr.from_bytes(link_modules(hugr1.to_bytes(), hugr2.to_bytes()))
    assert linked.entrypoint == linked.module_root


def test_entrypoint_lhs():
    hugr1 = build_module(entrypoint=True)
    hugr2 = build_module(entrypoint=False)

    linked = Hugr.from_bytes(link_modules(hugr1.to_bytes(), hugr2.to_bytes()))
    assert linked.entrypoint != linked.module_root
    entrypoint = linked.entrypoint_op()
    assert isinstance(entrypoint, FuncDefn)
    assert entrypoint.f_name == "main"


def test_entrypoint_rhs():
    hugr1 = build_module(entrypoint=False)
    hugr2 = build_module(entrypoint=True)

    linked = Hugr.from_bytes(link_modules(hugr1.to_bytes(), hugr2.to_bytes()))
    assert linked.entrypoint != linked.module_root
    entrypoint = linked.entrypoint_op()
    assert isinstance(entrypoint, FuncDefn)
    assert entrypoint.f_name == "main"


def test_multiple_entrypoints():
    hugr1 = build_module(entrypoint=True)
    hugr2 = build_module(entrypoint=True)

    with pytest.raises(ValueError, match="Cannot link two executable modules together"):
        link_modules(hugr1.to_bytes(), hugr2.to_bytes())
