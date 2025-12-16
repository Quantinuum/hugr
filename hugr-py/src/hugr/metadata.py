"""Typed metadata for HUGR nodes."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, ClassVar, Protocol, TypeVar, overload

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator

MetaCovariant = TypeVar("MetaCovariant", covariant=True)
Meta = TypeVar("Meta")


class Metadata(Protocol[MetaCovariant]):
    """Metadata for a HUGR node."""

    KEY: ClassVar[str]
    TYPE: ClassVar[type]


@dataclass
class NodeMetadata:
    """Key-value record of metadata for a HUGR node."""

    _dict: dict[str, Any]

    def __init__(self, metadata: dict[str, Any] | None = None) -> None:
        if metadata is None:
            metadata = {}
        self._dict = {
            k if isinstance(k, str) else k.KEY: v for k, v in metadata.items()
        }

    @overload
    def get(self, key: str, default: Any | None = None) -> Any | None: ...
    @overload
    def get(self, key: Metadata[Meta], default: Meta | None = None) -> Meta | None: ...
    def get(self, key: str | Metadata[Meta], default: Any | None = None) -> Meta | None:
        if not isinstance(key, str):
            key = key.KEY
        return self._dict.get(key, default)

    def items(self) -> Iterable[tuple[str, Any]]:
        return self._dict.items()

    def as_dict(self) -> dict[str, Any]:
        return self._dict

    @overload
    def __getitem__(self, key: str) -> Any: ...
    @overload
    def __getitem__(self, key: Metadata[Meta]) -> Meta: ...
    def __getitem__(self, key: str | Metadata[Meta]) -> Any:
        if not isinstance(key, str):
            key = key.KEY
        return self._dict[key]

    @overload
    def __setitem__(self, key: str, value: Any) -> None: ...
    @overload
    def __setitem__(self, key: Metadata[Meta], value: Meta) -> None: ...
    def __setitem__(self, key: str | Metadata[Meta], value: Any) -> None:
        if not isinstance(key, str):
            if not isinstance(value, key.TYPE):
                error = f"Value for metadata key {key.KEY} must be of type {key.TYPE}"
                raise TypeError(error)
            key = key.KEY
        self._dict[key] = value

    def __iter__(self) -> Iterator[str]:
        return iter(self._dict)

    def __len__(self) -> int:
        return len(self._dict)

    def __contains__(self, key: str | Metadata[Meta]) -> bool:
        if not isinstance(key, str):
            key = key.KEY
        return key in self._dict

    def __repr__(self) -> str:
        return f"NodeMetadata({self._dict})"
