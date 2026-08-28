"""HUGR prelude values."""

from __future__ import annotations

from dataclasses import dataclass

from hugr import ext, val
from hugr.std._util import _load_extension

PRELUDE_EXTENSION = _load_extension("prelude")

STRING_T_DEF = PRELUDE_EXTENSION.types["string"]

STRING_T = STRING_T_DEF.instantiate([])


@dataclass
class StringVal(val.ExtensionValue):
    """Custom value for a string."""

    v: str

    def to_value(self) -> val.Extension:
        name = "ConstString"
        return val.Extension(
            name,
            typ=STRING_T,
            val=self.v,
        )

    def __str__(self) -> str:
        return f"{self.v}"

    def _resolve_used_extensions_inplace(
        self,
        resolver: ext.UsedExtensionResolver,
        registry: ext.ExtensionRegistry | None = None,
    ) -> None:
        resolver.register(PRELUDE_EXTENSION)
