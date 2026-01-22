"""Collection types and operations."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

import hugr.tys as tys
from hugr import val
from hugr.std import _load_extension
from hugr.utils import comma_sep_str

if TYPE_CHECKING:
    from hugr.ext import ExtensionRegistry

EXTENSION = _load_extension("collections.list")


@dataclass(eq=False)
class List(tys.ExtType):
    """List type with a fixed element type."""

    def __init__(self, ty: tys.Type) -> None:
        ty_arg = tys.TypeTypeArg(ty)

        self.type_def = EXTENSION.types["List"]
        self.args = [ty_arg]

    @property
    def ty(self) -> tys.Type:
        """Returns the type of the list."""
        assert isinstance(
            self.args[0], tys.TypeTypeArg
        ), "List elements must have a valid type"
        return self.args[0].ty

    def type_bound(self) -> tys.TypeBound:
        return self.ty.type_bound()


@dataclass
class ListVal(val.ExtensionValue):
    """Constant value for a list of elements."""

    v: list[val.Value]
    ty: List

    def __init__(self, v: list[val.Value], elem_ty: tys.Type) -> None:
        self.v = v
        self.ty = List(elem_ty)

    def to_value(self) -> val.Extension:
        name = "ListValue"
        # The value list must be serialized at this point, otherwise the
        # `Extension` value would not be serializable.
        vs = [v._to_serial_root() for v in self.v]
        element_ty = self.ty.ty._to_serial_root()
        serial_val = {"values": vs, "typ": element_ty}
        return val.Extension(name, typ=self.ty, val=serial_val)

    def __str__(self) -> str:
        return f"[{comma_sep_str(self.v)}]"

    def _resolve_used_extensions_inplace(
        self, registry: ExtensionRegistry | None = None
    ) -> ExtensionRegistry:
        resolved_ty, reg = self.ty._resolve_used_extensions(registry)
        assert isinstance(resolved_ty, List)
        self.ty = resolved_ty
        for value in self.v:
            reg.extend(value._resolve_used_extensions_inplace(registry))
        return reg
