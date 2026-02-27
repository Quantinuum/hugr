from collections.abc import Iterable
from dataclasses import dataclass

import pytest

from hugr import tys, val
from hugr.build import Module
from hugr.hugr import Hugr, Node
from hugr.passes._scope import GlobalScope, InScope, LocalScope, PassScope


@dataclass(frozen=True)
class TestHugr:
    hugr: Hugr
    module_root: Node
    public_func: Node
    public_func_nested: Node
    private_func: Node
    public_func_decl: Node
    private_func_decl: Node
    const_def: Node


@pytest.fixture
def test_hugr() -> TestHugr:
    mod = Module()
    module_root = mod.hugr.module_root

    public_func = mod.define_function("public_func", [], [], visibility="Public")
    with public_func.add_nested() as public_func_nested:
        pass  # set outputs?

    private_func = mod.define_function("private_func", [], [])

    public_func_decl = mod.declare_function(
        "public_func_decl", tys.PolyFuncType([], tys.FunctionType([], []))
    )

    private_func_decl = mod.declare_function(
        "private_func_decl",
        tys.PolyFuncType([], tys.FunctionType([tys.Qubit], [tys.Qubit])),
        visibility="Private",
    )

    const_def = mod.add_const(val.TRUE)

    return TestHugr(
        hugr=mod.hugr,
        module_root=module_root,
        public_func=public_func.parent_node,
        public_func_nested=public_func_nested.parent_node,
        private_func=private_func.parent_node,
        public_func_decl=public_func_decl,
        private_func_decl=private_func_decl,
        const_def=const_def,
    )


@pytest.mark.parametrize(
    ("scope", "recursive"), [(LocalScope.FLAT, False), (LocalScope.RECURSIVE, True)]
)
def test_local_scope(test_hugr: TestHugr, scope: PassScope, recursive: bool):
    assert scope.recursive() == recursive

    # When the entrypoint is the module root,
    # the pass should not be applied to any regions.
    test_hugr.hugr.entrypoint = test_hugr.module_root
    assert scope.root(test_hugr.hugr) is None
    assert list(scope.regions(test_hugr.hugr)) == []
    for n, _ in test_hugr.hugr.nodes():
        assert scope.in_scope(test_hugr.hugr, n) == InScope.NO

    # Public function with a nested DFG
    test_hugr.hugr.entrypoint = test_hugr.public_func
    assert scope.root(test_hugr.hugr) == test_hugr.public_func
    expected_regions = (
        [test_hugr.public_func, test_hugr.public_func_nested]
        if recursive
        else [test_hugr.public_func]
    )
    assert list(scope.regions(test_hugr.hugr)) == expected_regions

    assert scope.in_scope(test_hugr.hugr, test_hugr.module_root) == InScope.NO
    assert (
        scope.in_scope(test_hugr.hugr, test_hugr.public_func)
        == InScope.PRESERVE_INTERFACE
    )

    assert scope.in_scope(test_hugr.hugr, test_hugr.public_func_nested) == InScope.YES

    for n in [
        test_hugr.module_root,
        test_hugr.private_func,
        test_hugr.public_func_decl,
        test_hugr.private_func_decl,
        test_hugr.const_def,
    ]:
        assert scope.in_scope(test_hugr.hugr, n) == InScope.NO

    # DFG inside a function
    test_hugr.hugr.entrypoint = test_hugr.public_func_nested
    assert scope.root(test_hugr.hugr) == test_hugr.public_func_nested
    assert list(scope.regions(test_hugr.hugr)) == [test_hugr.public_func_nested]

    for n in [
        test_hugr.module_root,
        test_hugr.public_func,
        test_hugr.private_func,
        test_hugr.public_func_decl,
        test_hugr.private_func_decl,
        test_hugr.const_def,
    ]:
        assert scope.in_scope(test_hugr.hugr, n) == InScope.NO
    assert (
        scope.in_scope(test_hugr.hugr, test_hugr.public_func_nested)
        == InScope.PRESERVE_INTERFACE
    )


def test_preserve_all(test_hugr: TestHugr):
    preserve = [
        test_hugr.public_func,
        test_hugr.private_func,
        test_hugr.public_func_decl,
        test_hugr.private_func_decl,
        test_hugr.const_def,
    ]
    check_preserve(test_hugr, GlobalScope.PRESERVE_ALL, preserve)


def check_preserve(
    test_hugr: TestHugr, scope: GlobalScope, expected_chs: Iterable[Node]
):
    assert scope.recursive()
    expected_chs = set(expected_chs)
    assert scope.root(test_hugr.hugr) == test_hugr.module_root
    assert set(scope.regions(test_hugr.hugr)) == {
        test_hugr.public_func,
        test_hugr.private_func,
        test_hugr.public_func_nested,
    }

    assert (
        scope.in_scope(test_hugr.hugr, test_hugr.module_root)
        == InScope.PRESERVE_INTERFACE
    )

    for n in [
        test_hugr.public_func,
        test_hugr.private_func,
        test_hugr.public_func_decl,
        test_hugr.public_func_nested,
        test_hugr.private_func_decl,
        test_hugr.const_def,
    ]:
        expected = InScope.PRESERVE_INTERFACE if n in expected_chs else InScope.YES
        assert scope.in_scope(test_hugr.hugr, n) == expected, f"{n} among {test_hugr}"

    expected_chs.add(test_hugr.module_root)  # Things to preserve
    assert set(scope.preserve_interface(test_hugr.hugr)) == expected_chs


def test_preserve_public(test_hugr: TestHugr):
    preserve = [test_hugr.public_func, test_hugr.public_func_decl]
    check_preserve(test_hugr, GlobalScope.PRESERVE_PUBLIC, preserve)


def test_preserve_entrypoint(test_hugr: TestHugr):
    test_hugr.hugr.entrypoint = test_hugr.hugr.module_root
    preserve = [test_hugr.public_func, test_hugr.public_func_decl]
    check_preserve(test_hugr, GlobalScope.PRESERVE_ENTRYPOINT, preserve)

    test_hugr.hugr.entrypoint = test_hugr.public_func_nested
    preserve = [test_hugr.public_func_nested]
    check_preserve(test_hugr, GlobalScope.PRESERVE_ENTRYPOINT, preserve)
