from __future__ import annotations

from typing import Any, ClassVar

import pytest
from semver import Version

from hugr import ops, tys
from hugr.build.function import Module
from hugr.debug_info import DICompileUnit, DILocation, DISubprogram
from hugr.envelope import EnvelopeConfig, ExtensionDesc, GeneratorDesc
from hugr.hugr import Hugr
from hugr.metadata import (
    HugrDebugInfo,
    HugrGenerator,
    HugrUsedExtensions,
    Metadata,
    NodeMetadata,
)
from hugr.utils import JsonType


class CustomMetadata(Metadata[list[JsonType]]):
    KEY = "custom.metadata"


class AliasedMetadata(Metadata[int]):
    KEY = "custom.metadata.new"
    ALIASES: ClassVar[list[str]] = ["custom.metadata.old", "custom.metadata.older"]

    @classmethod
    def from_json(cls, value: JsonType) -> int:
        if not isinstance(value, int):
            msg = f"Expected aliased metadata to be an int, but got {type(value)}"
            raise TypeError(msg)
        return value


def test_metadata_properties() -> None:
    hugr = Hugr[Any]()
    node = hugr[hugr.module_root]

    gen = GeneratorDesc(name="hugr-py-test", version=Version.parse("1.2.3"))
    node.metadata[HugrGenerator] = gen

    assert HugrGenerator in node.metadata
    assert HugrGenerator.KEY in node.metadata
    assert HugrUsedExtensions not in node.metadata
    assert HugrUsedExtensions.KEY not in node.metadata

    assert list(node.metadata) == [HugrGenerator.KEY]
    assert (
        str(node.metadata)
        == f"NodeMetadata({{'{HugrGenerator.KEY}': {gen.to_json()}}})"
    )


def test_metadata_roundtrip() -> None:
    hugr = Hugr[Any]()

    gen = GeneratorDesc(name="hugr-py-test", version=Version.parse("1.2.3"))
    exts = [
        ExtensionDesc(name="ext.a", version=Version.parse("0.1.0")),
        ExtensionDesc(name="ext.b", version=None),
    ]

    # Set the metadata on the module root node
    node = hugr[hugr.module_root]
    node.metadata[HugrGenerator] = gen
    node.metadata[HugrUsedExtensions] = exts

    custom_payload: list[JsonType] = [1, "payload", True, None, {"key": "value"}]
    node.metadata[CustomMetadata.KEY] = custom_payload
    node.metadata[CustomMetadata] = custom_payload

    # Roundtrip serialization
    data = hugr.to_bytes(EnvelopeConfig.TEXT)
    loaded = Hugr.from_bytes(data)
    node = loaded[loaded.module_root]

    # Typed readback
    assert node.metadata[HugrGenerator] == gen
    assert node.metadata.get(HugrGenerator) == gen
    assert node.metadata[HugrUsedExtensions] == exts
    assert node.metadata.get(HugrUsedExtensions) == exts
    assert node.metadata[CustomMetadata] == custom_payload
    assert node.metadata[CustomMetadata.KEY] == custom_payload
    assert node.metadata.get(CustomMetadata.KEY) == custom_payload
    assert node.metadata.get(CustomMetadata.KEY, "default") == custom_payload

    # Check the raw JSON encoding
    raw = node.metadata.as_dict()
    assert raw[HugrGenerator.KEY] == {"name": "hugr-py-test", "version": "1.2.3"}
    assert raw[HugrUsedExtensions.KEY] == [
        {"name": "ext.a", "version": "0.1.0"},
        {"name": "ext.b", "version": "0.0.0"},
    ]
    assert raw["custom.metadata"] == custom_payload


def test_metadata_default() -> None:
    hugr = Hugr[Any]()
    node = hugr[hugr.module_root]

    assert node.metadata.get(HugrGenerator) is None
    assert node.metadata.get(
        HugrGenerator, GeneratorDesc("hugr-py-test", Version.parse("1.2.3"))
    ) == GeneratorDesc("hugr-py-test", Version.parse("1.2.3"))
    assert node.metadata.get("missing.metadata") is None
    assert node.metadata.get("missing.metadata", [1, 2, 3]) == [1, 2, 3]


def test_metadata_aliases() -> None:
    metadata = NodeMetadata(
        {
            "custom.metadata.older": 1,
            "custom.metadata.old": 2,
        }
    )

    assert AliasedMetadata in metadata
    assert metadata[AliasedMetadata] == 2
    assert metadata.get(AliasedMetadata) == 2
    assert metadata.get(AliasedMetadata.KEY) is None

    metadata[AliasedMetadata] = 3
    assert metadata[AliasedMetadata] == 3
    assert metadata[AliasedMetadata.KEY] == 3

    metadata[AliasedMetadata.KEY] = "not an int"
    with pytest.raises(TypeError):
        metadata[AliasedMetadata]


def test_debug_info_roundtrip() -> None:
    mod = Module()

    # Add DICompileUnit debug info to the module root
    compile_unit = DICompileUnit(
        directory="/user/project/",
        filename=0,
        file_table=["guppy1.py", "guppy2.py"],
    )
    mod.hugr[mod.hugr.module_root].metadata[HugrDebugInfo] = compile_unit

    # Add a FuncDefn node to test DISubprogram debug info
    func = mod.define_function("random_func", [tys.Bool], [tys.Bool])
    [b] = func.inputs()
    func.set_outputs(b)
    subprogram = DISubprogram(file=0, line_no=10, scope_line=11)
    mod.hugr[func.parent_node].metadata[HugrDebugInfo] = subprogram

    # Add a call node test DILocation debug info
    caller = mod.define_function("caller", [tys.Bool], [tys.Bool])
    [b] = caller.inputs()
    call_node = caller.call(func.parent_node, b)
    caller.set_outputs(call_node)
    location = DILocation(column=5, line_no=20)
    mod.hugr[call_node].metadata[HugrDebugInfo] = location

    # Roundtrip serialization
    data = mod.hugr.to_bytes(EnvelopeConfig.TEXT)
    loaded = Hugr.from_bytes(data)
    module_node = loaded[loaded.module_root]

    assert module_node.metadata[HugrDebugInfo] == compile_unit

    [func_n, caller_n] = loaded.children(loaded.module_root)
    assert loaded[func_n].metadata[HugrDebugInfo] == subprogram

    call_n = next(
        n for n in loaded.children(caller_n) if isinstance(loaded[n].op, ops.Call)
    )
    assert loaded[call_n].metadata[HugrDebugInfo] == location
