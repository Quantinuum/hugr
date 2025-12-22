"""Typed metadata for HUGR nodes."""

from __future__ import annotations

import copy
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, ClassVar, Protocol, TypeVar, overload

import hugr._hugr.metadata as rust_metadata
from hugr.envelope import ExtensionDesc, GeneratorDesc

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator

Meta = TypeVar("Meta")


class Metadata(Protocol[Meta]):
    """Metadata for a HUGR node.

    This is a protocol for metadata entries that defines a unique key to
    identify the entry, and the type of the value.

    Values in a hugr are encoded using json. When the value type is not a
    primitive type, `to_json` and `from_json` must be implemented to serialize
    and deserialize the value.

    Args:
        value: The value of the metadata.
    """

    KEY: ClassVar[str]

    @classmethod
    def to_json(cls, value: Meta) -> Any:
        """Serialize the metadata value to a json value."""
        return value

    @classmethod
    def from_json(cls, value: Any) -> Meta:
        """Deserialize the metadata value from the stored json value."""
        return value


@dataclass
class NodeMetadata:
    """Key-value record of metadata for a HUGR node."""

    _dict: dict[str, Any]

    def __init__(self, metadata: dict[str, Any] | None = None) -> None:
        if metadata is None:
            metadata = {}
        # Only a shallow copy, values may still be shared with the original dictionary.
        self._dict = copy.copy(metadata)

    @overload
    def get(self, key: str, default: Any | None = None) -> Any | None: ...
    @overload
    def get(self, key: type[Metadata[Meta]], default: Meta) -> Meta: ...
    @overload
    def get(self, key: type[Metadata[Meta]], default: None = None) -> Meta | None: ...
    def get(
        self, key: str | type[Metadata[Meta]], default: Any | None = None
    ) -> Any | None:
        if isinstance(key, str):
            return self._dict.get(key, default)
        elif key.KEY in self._dict:
            val = self._dict[key.KEY]
            return key.from_json(val)
        else:
            return default

    def items(self) -> Iterable[tuple[str, Any]]:
        return self._dict.items()

    def as_dict(self) -> dict[str, Any]:
        return self._dict

    @overload
    def __getitem__(self, key: str) -> Any: ...
    @overload
    def __getitem__(self, key: type[Metadata[Meta]]) -> Meta: ...
    def __getitem__(self, key: str | type[Metadata[Meta]]) -> Any:
        if isinstance(key, str):
            return self._dict[key]
        else:
            val = self._dict[key.KEY]
            return key.from_json(val)

    @overload
    def __setitem__(self, key: str, value: Any) -> None: ...
    @overload
    def __setitem__(self, key: type[Metadata[Meta]], value: Meta) -> None: ...
    def __setitem__(self, key: str | type[Metadata[Meta]], value: Any) -> None:
        if isinstance(key, str):
            self._dict[key] = value
        else:
            json_value = key.to_json(value)
            self._dict[key.KEY] = json_value

    def __iter__(self) -> Iterator[str]:
        return iter(self._dict)

    def __len__(self) -> int:
        return len(self._dict)

    def __contains__(self, key: str | type[Metadata[Meta]]) -> bool:
        if not isinstance(key, str):
            key = key.KEY
        return key in self._dict

    def __repr__(self) -> str:
        return f"NodeMetadata({self._dict})"

    def __copy__(self) -> NodeMetadata:
        return NodeMetadata(copy.copy(self._dict))

    def __deepcopy__(self, memo: dict[int, Any]) -> NodeMetadata:
        return NodeMetadata(copy.deepcopy(self._dict, memo))


# --- Core metadata keys ---


class HugrGenerator(Metadata[GeneratorDesc]):
    """Metadata describing the generator that defined the HUGR module.

    This value is only valid when set at the module root node.
    """

    KEY = rust_metadata.HUGR_GENERATOR

    @classmethod
    def to_json(cls, value: GeneratorDesc) -> dict[str, str]:
        return value._to_json()

    @classmethod
    def from_json(cls, value: Any) -> GeneratorDesc:
        return GeneratorDesc._from_json(value)


class HugrUsedExtensions(Metadata[list[ExtensionDesc]]):
    """Metadata storing the list of extensions required to define the HUGR.

    This list may contain additional extensions that are no longer present in
    the Hugr.

    This value is only valid when set at the module root node.
    """

    KEY = rust_metadata.HUGR_USED_EXTENSIONS

    @classmethod
    def to_json(cls, value: list[ExtensionDesc]) -> list[dict[str, str]]:
        return [e._to_json() for e in value]

    @classmethod
    def from_json(cls, value: Any) -> list[ExtensionDesc]:
        if not isinstance(value, list):
            msg = (
                "Expected UsedExtensions metadata to be a list,"
                + f" but got {type(value)}"
            )
            raise TypeError(msg)
        return [ExtensionDesc._from_json(e) for e in value]
