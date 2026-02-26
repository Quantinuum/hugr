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
def test_hug() -> TestHugr:
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
def test_local_scope(test_hug: TestHugr, scope: PassScope, recursive: bool):
    assert scope.recursive() == recursive

    # When the entrypoint is the module root,
    # the pass should not be applied to any regions.
    test_hug.hugr.entrypoint = test_hug.module_root
    assert scope.root(test_hug.hugr) is None
    assert list(scope.regions(test_hug.hugr)) == []
    for n, _ in test_hug.hugr.nodes():
        assert scope.in_scope(test_hug.hugr, n) == InScope.NO

    # Public function with a nested DFG
    test_hug.hugr.entrypoint = test_hug.public_func
    assert scope.root(test_hug.hugr) == test_hug.public_func
    expected_regions = (
        [test_hug.public_func, test_hug.public_func_nested]
        if recursive
        else [test_hug.public_func]
    )
    assert list(scope.regions(test_hug.hugr)) == expected_regions

    assert scope.in_scope(test_hug.hugr, test_hug.module_root) == InScope.NO
    assert (
        scope.in_scope(test_hug.hugr, test_hug.public_func)
        == InScope.PRESERVE_INTERFACE
    )

    assert scope.in_scope(test_hug.hugr, test_hug.public_func_nested) == InScope.YES

    for n in [
        test_hug.module_root,
        test_hug.private_func,
        test_hug.public_func_decl,
        test_hug.private_func_decl,
        test_hug.const_def,
    ]:
        assert scope.in_scope(test_hug.hugr, n) == InScope.NO

    # DFG inside a function
    test_hug.hugr.entrypoint = test_hug.public_func_nested
    assert scope.root(test_hug.hugr) == test_hug.public_func_nested
    assert list(scope.regions(test_hug.hugr)) == [test_hug.public_func_nested]

    for n in [
        test_hug.module_root,
        test_hug.public_func,
        test_hug.private_func,
        test_hug.public_func_decl,
        test_hug.private_func_decl,
        test_hug.const_def,
    ]:
        assert scope.in_scope(test_hug.hugr, n) == InScope.NO
    assert (
        scope.in_scope(test_hug.hugr, test_hug.public_func_nested)
        == InScope.PRESERVE_INTERFACE
    )


def test_preserve_all(test_hug: TestHugr):
    preserve = [
        test_hug.public_func,
        test_hug.private_func,
        test_hug.public_func_decl,
        test_hug.private_func_decl,
        test_hug.const_def,
    ]
    check_preserve(test_hug, GlobalScope.PRESERVE_ALL, preserve)


def check_preserve(
    test_hug: TestHugr, scope: GlobalScope, expected_chs: Iterable[Node]
):
    assert scope.recursive()
    expected_chs = set(expected_chs)
    assert scope.root(test_hug.hugr) == test_hug.module_root
    assert set(scope.regions(test_hug.hugr)) == {
        test_hug.public_func,
        test_hug.private_func,
        test_hug.public_func_nested,
    }

    assert (
        scope.in_scope(test_hug.hugr, test_hug.module_root)
        == InScope.PRESERVE_INTERFACE
    )

    for n in [
        test_hug.public_func,
        test_hug.private_func,
        test_hug.public_func_decl,
        test_hug.public_func_nested,
        test_hug.private_func_decl,
        test_hug.const_def,
    ]:
        expected = InScope.PRESERVE_INTERFACE if n in expected_chs else InScope.YES
        assert scope.in_scope(test_hug.hugr, n) == expected, f"{n} among {test_hug}"

    expected_chs.add(test_hug.module_root)  # Things to preserve
    assert set(scope.preserve_interface(test_hug.hugr)) == expected_chs


def test_preserve_public(test_hug: TestHugr):
    preserve = [test_hug.public_func, test_hug.public_func_decl]
    check_preserve(test_hug, GlobalScope.PRESERVE_PUBLIC, preserve)


def test_preserve_entrypoint(test_hug: TestHugr):
    test_hug.hugr.entrypoint = test_hug.hugr.module_root
    preserve = [test_hug.public_func, test_hug.public_func_decl]
    check_preserve(test_hug, GlobalScope.PRESERVE_ENTRYPOINT, preserve)

    test_hug.hugr.entrypoint = test_hug.public_func_nested
    preserve = [test_hug.public_func_nested]
    check_preserve(test_hug, GlobalScope.PRESERVE_ENTRYPOINT, preserve)
