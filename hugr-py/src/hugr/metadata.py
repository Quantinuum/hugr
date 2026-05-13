"""Typed metadata for HUGR nodes."""

from __future__ import annotations

import copy
from collections.abc import Mapping
from dataclasses import dataclass
from typing import (
    TYPE_CHECKING,
    Any,
    ClassVar,
    Protocol,
    TypeVar,
    overload,
)

import hugr._hugr.metadata as rust_metadata
from hugr.debug_info import DebugRecord
from hugr.envelope import ExtensionDesc, GeneratorDesc

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator

    from hugr.utils import JsonType


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
    """The unique key associated with the metadata entry."""

    ALIASES: ClassVar[list[str]] = []
    """Other aliases of the metadata key.

    Typed metadata reads use these, in order, as fallbacks when KEY is not
    present. This is used for backward compatibility when renaming metadata
    keys.

    Writes ignore this field and only write to KEY.
    """

    @classmethod
    def to_json(cls, value: Meta) -> JsonType:
        """Serialize the metadata value to a json value."""
        # Recursive types cannot be checked by isinstance, so we can only use a
        # surface level check.
        assert isinstance(
            value, str | int | float | bool | None | Mapping | list
        ), f"Cannot serialize {cls.KEY} metadata value {value} to json."
        return value

    @classmethod
    def from_json(cls, value: JsonType) -> Meta:
        """Deserialize the metadata value from the stored json value."""
        # Default implementation for primitive types.
        #
        # `Meta` not runtime checkable, so we need to use type: ignore.
        return value  # type: ignore  # noqa: PGH003


@dataclass
class NodeMetadata:
    """Key-value record of metadata for a HUGR node."""

    _dict: dict[str, JsonType]

    def __init__(self, metadata: dict[str, JsonType] | None = None) -> None:
        """Create a metadata record from an optional raw metadata dictionary."""
        if metadata is None:
            metadata = {}
        # Only a shallow copy, values may still be shared with the original dictionary.
        self._dict = copy.copy(metadata)

    @staticmethod
    def _keys_for_metadata(key: type[Metadata[Meta]]) -> Iterable[str]:
        """Return the raw metadata keys used when reading typed metadata."""
        return (key.KEY, *key.ALIASES)

    def _typed_json(self, key: type[Metadata[Meta]]) -> JsonType:
        """Return the stored JSON value for a typed metadata entry."""
        for raw_key in self._keys_for_metadata(key):
            if raw_key in self._dict:
                return self._dict[raw_key]
        raise KeyError(key.KEY)

    @overload
    def get(self, key: type[Metadata[Meta]], default: Meta) -> Meta: ...
    @overload
    def get(self, key: type[Metadata[Meta]], default: None = None) -> Meta | None: ...
    @overload
    def get(self, key: str, default: JsonType | None = None) -> JsonType | None: ...
    def get(
        self, key: str | type[Metadata[Meta]], default: Any | None = None
    ) -> Meta | JsonType | None:
        """Return a metadata value, or a default if the key is missing.

        When `key` is a string, it is looked up directly in the raw metadata
        dictionary. When `key` is a typed `Metadata` class, the metadata is
        looked up using `key.KEY` first, then each entry in `key.ALIASES` in
        order.

        Typed values are deserialized with `key.from_json` before being
        returned.
        """
        if isinstance(key, str):
            return self._dict.get(key, default)
        else:
            try:
                val = self._typed_json(key)
            except KeyError:
                return default
            return key.from_json(val)

    def items(self) -> Iterable[tuple[str, JsonType]]:
        """Return an iterable over the raw metadata key-value pairs."""
        return self._dict.items()

    def as_dict(self) -> dict[str, JsonType]:
        """Return the underlying raw metadata dictionary."""
        return self._dict

    @overload
    def __getitem__(self, key: str) -> JsonType: ...
    @overload
    def __getitem__(self, key: type[Metadata[Meta]]) -> Meta: ...
    def __getitem__(self, key: str | type[Metadata[Meta]]) -> JsonType | Meta:
        """Return a raw or typed metadata value.

        String keys are looked up directly. Typed metadata keys use their
        primary key and aliases, and deserialize the stored JSON value before
        returning it.
        """
        if isinstance(key, str):
            return self._dict[key]
        else:
            val = self._typed_json(key)
            return key.from_json(val)

    @overload
    def __setitem__(self, key: str, value: JsonType) -> None: ...
    @overload
    def __setitem__(self, key: type[Metadata[Meta]], value: Meta) -> None: ...
    def __setitem__(
        self, key: str | type[Metadata[Meta]], value: JsonType | Meta
    ) -> None:
        """Set a raw or typed metadata value.

        String keys store JSON values directly. Typed metadata keys serialize
        values with `key.to_json` and always write to `key.KEY`; aliases are
        ignored when writing.
        """
        if isinstance(key, str):
            # Recursive types cannot be checked by isinstance, so we can only use a
            # surface level check.
            assert isinstance(
                value, str | int | float | bool | None | Mapping | list
            ), f"Cannot set {key} metadata key with non-json value {value}."
            self._dict[key] = value
        else:
            # `value` must be a `Meta` type. Since `Meta` is not runtime checkable,
            # we need to use type: ignore.
            json_value = key.to_json(value)  # type: ignore  # noqa: PGH003
            self._dict[key.KEY] = json_value

    def __iter__(self) -> Iterator[str]:
        """Iterate over the raw metadata keys."""
        return iter(self._dict)

    def __len__(self) -> int:
        """Return the number of raw metadata entries."""
        return len(self._dict)

    def __contains__(self, key: str | type[Metadata[Meta]]) -> bool:
        """Return whether a raw or typed metadata key is present.

        Typed metadata keys match either their primary key or any alias.
        """
        if isinstance(key, str):
            return key in self._dict
        return any(raw_key in self._dict for raw_key in self._keys_for_metadata(key))

    def __repr__(self) -> str:
        return f"NodeMetadata({self._dict})"

    def __copy__(self) -> NodeMetadata:
        return NodeMetadata(copy.copy(self._dict))

    def __deepcopy__(self, memo: dict[int, JsonType]) -> NodeMetadata:
        return NodeMetadata(copy.deepcopy(self._dict, memo))


# --- Core metadata keys ---


class HugrGenerator(Metadata[GeneratorDesc]):
    """Metadata describing the generator that defined the HUGR module.

    This value is only valid when set at the module root node.
    """

    KEY = rust_metadata.HUGR_GENERATOR

    @classmethod
    def to_json(cls, value: GeneratorDesc) -> dict[str, str]:
        return value.to_json()

    @classmethod
    def from_json(cls, value: JsonType) -> GeneratorDesc:
        return GeneratorDesc.from_json(value)


class HugrUsedExtensions(Metadata[list[ExtensionDesc]]):
    """Metadata storing the list of extensions required to define the HUGR.

    This list may contain additional extensions that are no longer present in
    the Hugr.

    This value is only valid when set at the module root node.
    """

    KEY = rust_metadata.HUGR_USED_EXTENSIONS

    @classmethod
    def to_json(cls, value: list[ExtensionDesc]) -> JsonType:
        return [e.to_json() for e in value]

    @classmethod
    def from_json(cls, value: JsonType) -> list[ExtensionDesc]:
        if not isinstance(value, list):
            msg = (
                "Expected UsedExtensions metadata to be a list,"
                + f" but got {type(value)}"
            )
            raise TypeError(msg)
        return [ExtensionDesc.from_json(e) for e in value]


class HugrDebugInfo(Metadata[DebugRecord]):
    """Metadata storing debug information obtained from the generator source."""

    KEY = rust_metadata.HUGR_DEBUG_INFO

    @classmethod
    def to_json(cls, value: DebugRecord) -> JsonType:
        return value.to_json()

    @classmethod
    def from_json(cls, value: JsonType) -> DebugRecord:
        return DebugRecord.from_json(value)
