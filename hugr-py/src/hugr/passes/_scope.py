"""Scope configuration for a pass.

A `PassScope` defines the parts of a HUGR that a pass should be applied to, and
which parts is it allowed to modify. Each variant defines three properties: `root`,
`preserve_interface` and `recursive`.

From these, `regions` and `in_scope` can be derived.

A pass will always optimize the entrypoint region, unless the entrypoint is the
module root.
"""

from __future__ import annotations

from abc import ABC, ABCMeta, abstractmethod
from collections import deque
from enum import Enum, EnumMeta
from typing import TYPE_CHECKING

from hugr import ops

if TYPE_CHECKING:
    from collections.abc import Iterable

    from hugr.hugr.base import Hugr
    from hugr.hugr.node_port import Node


class InScope(Enum):
    """Whether a pass may modify a particular node."""

    YES = "YES"
    """The pass may modify the node arbitrarily, including changing its interface,
    behaviour, and/or removing it altogether"""

    PRESERVE_INTERFACE = "PRES_INT"
    """The pass may modify the interior of the node - its `OpType`, and its
    descendants - but must maintain the same ports (including static and `ControlFlow`
    ports), function name and visibility, and execution behaviour.

    For the module root, this is equivalent to `NO`."""

    NO = "NO"
    """The pass may not modify this node"""


class PassScopeBase(ABC):
    """Abstract superclass for concrete implementations of `PassScope`."""

    @abstractmethod
    def root(self, hugr: Hugr) -> Node | None:
        """Returns the root of the subtree to be optimized by the pass,
        or none if the pass should do nothing.
        """

    @abstractmethod
    def preserve_interface(self, hugr: Hugr) -> Iterable[Node]:
        """Returns a list of nodes, in the subtree beneath `root`, for which
        the pass must preserve the observable semantics (ports, execution behaviour,
        linking).

        We include the `Module` in this list (if it is `root`) as these
        properties must be preserved (this rules out any other changes).
        """

    @abstractmethod
    def recursive(self) -> bool:
        """Returns `true` if the pass should be applied recursively on the
        descendants of the root regions.
        """

    def regions(self, hugr: Hugr) -> Iterable[Node]:
        """Return every region (every [dataflow] or [CFG] container - but excluding
        `Module`) in the Hugr to be optimized by the pass.

        This computes all the regions to be optimized at once. In general, it is
        more efficient to traverse the Hugr incrementally starting from the
        `PassScope.root` instead.
        """
        if (r := self.root(hugr)) is None:
            return
        if r == hugr.module_root:
            assert self.recursive()
        else:
            yield r
            if not self.recursive():
                return
        to_explore = deque(hugr.children(r))
        while to_explore:
            node = to_explore.popleft()
            if hugr.children(node):
                yield node
                to_explore.extend(hugr.children(node))

    def in_scope(self, hugr: Hugr, n: Node) -> InScope:
        """Returns whether the node may be modified by the pass.

        Nodes outside the `root` subtree are never in scope.
        Nodes inside the subtree may be `InScope.YES` or `InScope.PRESERVE_INTERFACE`.
        """
        if (r := self.root(hugr)) is None:
            return InScope.NO
        if r != hugr.module_root:
            anc: Node | None = n
            while True:
                if anc is None:
                    return InScope.NO
                if anc == r:
                    break
                anc = hugr[anc].parent
        return (
            InScope.PRESERVE_INTERFACE
            if n in self.preserve_interface(hugr)
            else InScope.YES
        )


class ABCEnumMeta(ABCMeta, EnumMeta):
    """Custom metaclass for things that inherit from both `ABC` and `Enum`.

    This is to solve the error:
    `Metaclass conflict: the metaclass of a derived class must be a (non-strict)
    subclass of the metaclasses of all its bases  [metaclass]`
    """


class LocalScope(PassScopeBase, Enum, metaclass=ABCEnumMeta):
    """A `PassScope` that means the pass should modify the hugr only
    beneath the entrypoint, unless the entrypoint is the module root,
    in which case the pass should do nothing.

    - `root`: The entrypoint, unless that is the module root.
    - `preserve_interface`: the entrypoint, unless that is the module root
    """

    FLAT = "EntrypointFlat"
    """Run the pass only on the entrypoint region.

    If the entrypoint is the module root, does nothing.

    The pass is allowed, but not required, to optimize descendant regions too.
    (For passes where it makes sense to distinguish flat from `EntrypointRecursive`,
    this is encouraged, but for many passes it does not make sense so both `EntrypointXXX`
    variants may behave the same.)

    - `recursive`: `false`.
    """

    RECURSIVE = "EntrypointRecursive"
    """Run the pass on the entrypoint region and all its descendants.

    For an idempotent pass, this means that immediately rerunning the pass on
    any subregion (i.e. with the entrypoint set to any descendant of
    the current value), must have no effect.

    If the entrypoint is the module root, does nothing.

    - `recursive`: `true`.
    """

    def root(self, hugr: Hugr) -> Node | None:
        return None if hugr.entrypoint == hugr.module_root else hugr.entrypoint

    def preserve_interface(self, hugr: Hugr) -> Iterable[Node]:
        if (r := self.root(hugr)) is not None:
            yield r

    def recursive(self) -> bool:
        return self == LocalScope.RECURSIVE


class GlobalScope(PassScopeBase, Enum, metaclass=ABCEnumMeta):
    """Run the pass on the whole Hugr, regardless of the entrypoint.

    For lowering passes, signature changes etc. should be applied across the Hugr.

    For optimization passes, different variants specify which nodes in the Hugr
    must have their interface preserved. (Interface means signature/value ports,
    as well as static ports, and their types; also name (if public) for linking;
    and whether the node is a valid dataflow child or is a `DataflowBlock`,
    `ExitBlock` or `Module`).

    - `root`: The hugr module_root
    - `recursive`: true
    """

    PRESERVE_ALL = "GlobalAll"
    """Optimization passes must preserve interface and behaviour of every module child,
    as well as the entrypoint.

    - `preserve_interface`: every public function defined in the module,
       and the entrypoint."""

    PRESERVE_PUBLIC = "GlobalPublic"
    """Optimization passes must preserve interface and behaviour of all public
    functions, as well as the entrypoint.

    Private functions and constant definitions may be modified, including
    changing their behaviour or deleting them entirely, so long as this
    does not affect behaviour of the public functions (or entrypoint).

    Thus, appropriate for a Hugr that will be linked as a library.

    - `preserve_interface`: Every public function defined in the module', plus
      the entrypoint."""

    PRESERVE_ENTRYPOINT = "GlobalEntrypoint"
    """Run the pass on the whole Hugr, but preserving behaviour only of the entrypoint.

    Thus, appropriate for a Hugr that will be run as an executable, with the entrypoint
    indicating where execution will begin.

    If the entrypoint is the module root, then the same as [Self::Public].

    - `preserve_interface`: if the entrypoint node is the module root, then all
       children of the module root; otherwise, just the entrypoint node."""

    def root(self, hugr: Hugr) -> Node:
        return hugr.module_root

    def recursive(self) -> bool:
        return True

    def preserve_interface(self, hugr: Hugr) -> Iterable[Node]:
        yield hugr.module_root
        ep = hugr.entrypoint
        if ep != hugr.module_root:
            yield ep
            if self == GlobalScope.PRESERVE_ENTRYPOINT:
                return  # That's all, folks
        for n in hugr.children(hugr.module_root):
            if n == ep:
                continue
            match self:
                case GlobalScope.PRESERVE_ALL:
                    pass
                case (
                    GlobalScope.PRESERVE_ENTRYPOINT  # entrypoint == module_root above
                    | GlobalScope.PRESERVE_PUBLIC
                ):
                    op = hugr[n].op
                    match op:
                        case ops.FuncDefn():
                            if op.visibility != "Public":
                                continue
                        case ops.FuncDecl():
                            if op.visibility != "Public":
                                continue
                        case _:
                            pass
            yield n


# Should be kept in sync with the `PassScope` enum in `hugr-passes`.
PassScope = LocalScope | GlobalScope
