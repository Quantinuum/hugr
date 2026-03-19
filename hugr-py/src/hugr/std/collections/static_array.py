"""Statically sized immutable array type and its operations."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from hugr import tys, val
from hugr.std._util import _load_extension
from hugr.utils import comma_sep_str

if TYPE_CHECKING:
    from hugr.ext import ExtensionRegistry, ExtensionResolutionResult

EXTENSION = _load_extension("collections.static_array")


@dataclass(eq=False)
class StaticArray(tys.ExtType):
    """Fixed size immutable array of `ty` elements."""

    def __init__(self, ty: tys.Type) -> None:
        self.type_def = EXTENSION.types["static_array"]
        if (
            tys.TypeBound.join(ty.type_bound(), tys.TypeBound.Copyable)
            != tys.TypeBound.Copyable
        ):
            msg = "Static array elements must be copyable"
            raise ValueError(msg)
        self.args = [tys.TypeTypeArg(ty)]

    @property
    def ty(self) -> tys.Type:
        assert isinstance(
            self.args[0], tys.TypeTypeArg
        ), "Array elements must have a valid type"
        return self.args[0].ty

    def type_bound(self) -> tys.TypeBound:
        return self.ty.type_bound()

    def _resolve_used_extensions(
        self, registry: ExtensionRegistry | None = None
    ) -> tuple[StaticArray, ExtensionResolutionResult]:
        ext_type, result = super()._resolve_used_extensions(registry)

        assert isinstance(
            ext_type, tys.ExtType
        ), "HUGR internal error, expected resolved type to be extension type."
        assert (
            ext_type.type_def == EXTENSION.types["static_array"]
        ), "HUGR internal error, expected resolved type to be static array."

        static_array = StaticArray(tys.Unit)
        static_array.args = ext_type.args
        return static_array, result


@dataclass
class StaticArrayVal(val.ExtensionValue):
    """Constant value for a statically sized immutable array of elements."""

    v: list[val.Value]
    ty: StaticArray
    name: str

    def __init__(self, v: list[val.Value], elem_ty: tys.Type, name: str) -> None:
        self.v = v
        self.ty = StaticArray(elem_ty)
        self.name = name

    def to_value(self) -> val.Extension:
        # Encode the nested values as JSON strings directly, to mirror what
        # happens when loading (where we can't decode the constant payload back
        # into specialized `Value`s).
        serial_val = {
            "value": {
                "values": [v._to_serial_root() for v in self.v],
                "typ": self.ty.ty._to_serial_root(),
            },
            "name": self.name,
        }
        return val.Extension("StaticArrayValue", typ=self.ty, val=serial_val)

    def __str__(self) -> str:
        return f"static_array({comma_sep_str(self.v)})"

    def _resolve_used_extensions_inplace(
        self, registry: ExtensionRegistry | None = None
    ) -> ExtensionResolutionResult:
        resolved_ty, result = self.ty._resolve_used_extensions(registry)
        assert isinstance(
            resolved_ty, StaticArray
        ), "HUGR internal error, expected resolved type to be static array."
        self.ty = resolved_ty
        for value in self.v:
            result.extend(value._resolve_used_extensions_inplace(registry))
        return result
