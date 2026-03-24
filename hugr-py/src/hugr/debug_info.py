"""Typed debug information metadata for HUGR nodes, to be attached by the generator
in order to propagate information about the generator source throughout the compilation
stack.
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import ClassVar, cast

from hugr.utils import JsonType


@dataclass
class DebugRecord(ABC):
    """Abstract base class for debug records."""

    @abstractmethod
    def to_json(self) -> JsonType:
        """Encodes the record as a dictionary of native types that can be serialized by
        `json.dump`.
        """

    @classmethod
    def from_json(cls, value: JsonType) -> "DebugRecord":
        """Decode a debug record from json. This is not an abstract method because when
        decoding from json by calling `DebugRecord.from_json` we do not have concrete
        subtype information, so we decode from the explicit variant tag stored in `kind`
        instead.
        """
        if not isinstance(value, dict):
            msg = f"Expected a dictionary for DebugRecord, but got {type(value)}"
            raise TypeError(msg)

        kind = value.get("kind")
        if isinstance(kind, str):
            if kind == DICompileUnit.KIND:
                return DICompileUnit.from_json(value)
            if kind == DISubprogram.KIND:
                return DISubprogram.from_json(value)
            if kind == DILocation.KIND:
                return DILocation.from_json(value)
            msg = f"Unknown DebugRecord kind: {kind}"
            raise TypeError(msg)

        msg = "Expected DebugRecord to contain string field 'kind'."
        raise TypeError(msg)


@dataclass
class DICompileUnit(DebugRecord):
    """Debug information for a compilation unit, corresponds to a HUGR module node."""

    KIND: ClassVar[str] = "compile_unit"

    directory: str  # Working directory of the compiler that generated the HUGR.
    filename: int  # File that contains the HUGR entrypoint.
    file_table: list[str]  # Global table of all files referenced in the module.

    def to_json(self) -> dict[str, JsonType]:
        return {
            "kind": self.KIND,
            "directory": self.directory,
            "filename": self.filename,
            "file_table": cast("list[JsonType]", self.file_table),
        }

    @classmethod
    def from_json(cls, value: JsonType) -> "DICompileUnit":
        if not isinstance(value, dict):
            msg = f"Expected a dictionary for DICompileUnit, but got {type(value)}"
            raise TypeError(msg)
        for key in ("kind", "directory", "filename", "file_table"):
            if key not in value:
                msg = f"Expected DICompileUnit to have a '{key}' key but got {value}"
                raise TypeError(msg)
        files = value["file_table"]
        if not isinstance(files, list):
            msg = f"Expected 'file_table' to be a list but got {type(files)}"
            raise TypeError(msg)
        return DICompileUnit(
            directory=str(value["directory"]),
            filename=int(value["filename"]),
            file_table=list[str](files),
        )


@dataclass
class DISubprogram(DebugRecord):
    """Debug information for a subprogram, corresponds to a function definition or
    declaration node.
    """

    KIND: ClassVar[str] = "subprogram"

    file: int  # Index into the string table for filenames.
    line_no: int  # First line of the function definition.
    scope_line: int | None = None  # First line of the function body.

    def to_json(self) -> dict[str, JsonType]:
        data: dict[str, JsonType] = {
            "kind": self.KIND,
            "file": self.file,
            "line_no": self.line_no,
        }
        # Declarations have no function body so could have no scope_line.
        if self.scope_line is not None:
            data["scope_line"] = self.scope_line
        return data

    @classmethod
    def from_json(cls, value: JsonType) -> "DISubprogram":
        if not isinstance(value, dict):
            msg = f"Expected a dictionary for DISubprogram, but got {type(value)}"
            raise TypeError(msg)
        for key in ("kind", "file", "line_no"):
            if key not in value:
                msg = f"Expected DISubprogram to have a '{key}' key but got {value}"
                raise TypeError(msg)
        # Declarations have no function body so could have no scope_line.
        scope_line = int(value["scope_line"]) if "scope_line" in value else None
        return DISubprogram(
            file=int(value["file"]),
            line_no=int(value["line_no"]),
            scope_line=scope_line,
        )


@dataclass
class DILocation(DebugRecord):
    """Debug information for a location, corresponds to call or extension operation
    node.
    """

    KIND: ClassVar[str] = "location"

    column: int
    line_no: int

    def to_json(self) -> dict[str, JsonType]:
        return {
            "kind": self.KIND,
            "column": self.column,
            "line_no": self.line_no,
        }

    @classmethod
    def from_json(cls, value: JsonType) -> "DILocation":
        if not isinstance(value, dict):
            msg = f"Expected a dictionary for DILocation, but got {type(value)}"
            raise TypeError(msg)
        for key in ("kind", "column", "line_no"):
            if key not in value:
                msg = f"Expected DILocation to have a '{key}' key but got {value}"
                raise TypeError(msg)
        return DILocation(column=int(value["column"]), line_no=int(value["line_no"]))
