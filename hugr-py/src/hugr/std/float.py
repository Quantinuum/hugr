"""Floating point types and operations."""

from __future__ import annotations

from dataclasses import dataclass

import hugr.model as model
from hugr import ext, val
from hugr.std._util import _load_extension

FLOAT_TYPES_EXTENSION = _load_extension("arithmetic.float.types")

FLOAT_T = FLOAT_TYPES_EXTENSION.types["float64"].instantiate([])


FLOAT_OPS_EXTENSION = _load_extension("arithmetic.float")


@dataclass
class FloatVal(val.ExtensionValue):
    """Custom value for a floating point number."""

    v: float

    def to_value(self) -> val.Extension:
        name = "ConstF64"
        payload = {"value": self.v}
        return val.Extension(name, typ=FLOAT_T, val=payload)

    def __str__(self) -> str:
        return f"{self.v}"

    def _resolve_used_extensions_inplace(
        self,
        resolver: ext.UsedExtensionResolver,
        registry: ext.ExtensionRegistry | None = None,
    ) -> None:
        resolver.register(FLOAT_TYPES_EXTENSION)

    def to_model(self) -> model.Term:
        return model.Apply("arithmetic.float.const_f64", [model.Literal(self.v)])
