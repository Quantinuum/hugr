"""Scope configuration for a pass.

This defines the parts of the HUGR that a pass should be applied to, and
which parts is it allowed to modify.
"""

from __future__ import annotations

from collections import deque
from enum import Enum
from typing import TYPE_CHECKING

from hugr import ops

if TYPE_CHECKING:
    from collections.abc import Iterable

    from hugr.hugr.base import Hugr
    from hugr.hugr.node_port import Node


class PassScope(Enum):
    """Scope configuration for a pass.

    The scope of a pass defines which parts of a HUGR it is allowed to modify.

    Each variant defines the following properties:
    - `roots` is a set of **regions** in the HUGR that the pass should be
      applied to.
      - The pass **MUST NOT** modify the container nodes of the regions defined
        in `roots`. This includes the optype and ports of the node.
    - `scope` is a set of **nodes** in the HUGR that the pass **MAY** modify.
      - This set is closed under descendants, meaning that all the descendants
        of a node in `scope` are also in scope.
      - Nodes that are not in `scope` **MUST** remain unchanged.
      - Regions parents defined in `roots` are never in scope, as they should
        not be modified.
      - The entrypoint node is never in scope.
    - `recursive` is a boolean flag indicating whether the pass **SHOULD**
      optimize the descendants of the regions in `roots`.
      - If this flag is `false`, the pass **MAY** still modify the descendant
        regions.

    A pass will always optimize the entrypoint region, unless it is set to the
    module root.
    """

    # This enum should be kept in sync with the `PassScope` enum in `hugr-passes`.

    ENTRYPOINT_FLAT = "EntrypointFlat"
    """Run the pass only on the entrypoint region.

    - `roots`: The entrypoint node, if it is not the module root.
    - `scope`: The descendants of the entrypoint node, if `entrypoint` is
      not the module root.
    - `recursive`: `false`.
    """

    ENTRYPOINT_RECURSIVE = "EntrypointRecursive"
    """Run the pass on the entrypoint region and all its descendants.

    - `roots`: The entrypoint node, if it is not the module root.
    - `scope`: The descendants of the entrypoint node, if `entrypoint` is
      not the module root.
    - `recursive`: `true`.
    """

    ALL = "All"
    """Run the pass on all regions and nodes in the Hugr.

    - `roots`: Every function defined in the module.
    - `scope`: The whole Hugr, except nodes in the module root region and
      the entrypoint node.
    - `recursive`: `true`.
    """

    ALL_PUBLIC = "AllPublic"
    """Run the pass on all public functions in the Hugr.

    Private functions and constant definitions may be modified, or even
    removed, by the pass.

    - `roots`: Every public function defined in the module.
    - `scope`: The whole Hugr, except public function definitions and
      declarations in the module root and the entrypoint node.
    - `recursive`: `true`.
    """

    def roots(self, hugr: Hugr) -> Iterable[Node]:
        """Returns the root nodes to be optimized by the pass."""
        match self:
            case PassScope.ENTRYPOINT_FLAT | PassScope.ENTRYPOINT_RECURSIVE:
                yield hugr.entrypoint
            case PassScope.ALL:
                for node in hugr.children(hugr.module_root):
                    if isinstance(hugr[node].op, ops.FuncDefn):
                        yield node
            case PassScope.ALL_PUBLIC:
                for node in hugr.children(hugr.module_root):
                    op = hugr[node].op
                    if isinstance(op, ops.FuncDefn) and op.visibility == "Public":
                        yield node

    def regions(self, hugr: Hugr) -> Iterable[Node]:
        """Returns the regions to be optimized by the pass."""
        to_explore = deque(self.roots(hugr))
        while to_explore:
            node = to_explore.popleft()
            yield node
            if self.recursive():
                to_explore.extend(n for n in hugr.children(node) if hugr.children(n))

    def in_scope(self, hugr: Hugr, node: Node) -> bool:
        """Returns whether the node is in scope for the pass."""
        # The root module node is never in scope.
        if node == hugr.module_root:
            return False
        # The entrypoint node is never in scope.
        if node == hugr.entrypoint:
            return False

        match self:
            case PassScope.ENTRYPOINT_FLAT | PassScope.ENTRYPOINT_RECURSIVE:
                if hugr.entrypoint == hugr.module_root:
                    return False
                # The node is in scope if one of its ancestors is the entrypoint.
                parent = hugr[node].parent
                while parent is not None:
                    if parent == hugr.entrypoint:
                        return True
                    parent = hugr[parent].parent
                return False

            case PassScope.ALL:
                # Any node not in the module root is in scope.
                return hugr[node].parent != hugr.module_root

            case PassScope.ALL_PUBLIC:
                if hugr[node].parent != hugr.module_root:
                    return True
                # For module children, only private functions
                # declarations/definitions and const are in scope.
                op = hugr[node].op
                match op:
                    case ops.FuncDefn():
                        return op.visibility == "Private"
                    case ops.FuncDecl():
                        return op.visibility == "Private"
                    case _:
                        return True

    def recursive(self) -> bool:
        """Returns whether the pass should be applied recursively on the
        descendants of the root regions.
        """
        match self:
            case PassScope.ENTRYPOINT_FLAT:
                return False
            case PassScope.ENTRYPOINT_RECURSIVE | PassScope.ALL | PassScope.ALL_PUBLIC:
                return True
