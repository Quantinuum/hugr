from __future__ import annotations

from typing import Any

from semver import Version

from hugr.envelope import EnvelopeConfig, ExtensionDesc, GeneratorDesc
from hugr.hugr import Hugr
from hugr.metadata import HugrGenerator, HugrUsedExtensions


def test_metadata_roundtrip() -> None:
    hugr = Hugr[Any]()

    gen = GeneratorDesc(name="hugr-py-test", version=Version.parse("1.2.3"))
    exts = [
        ExtensionDesc(name="ext.a", version=Version.parse("0.1.0")),
        ExtensionDesc(name="ext.b", version=Version.parse("2.0.0")),
    ]

    # Set the metadata on the module root node
    node = hugr[hugr.module_root]
    node.metadata[HugrGenerator] = gen
    node.metadata[HugrUsedExtensions] = exts

    # Roundtrip serialization
    data = hugr.to_bytes(EnvelopeConfig.TEXT)
    loaded = Hugr.from_bytes(data)
    node = loaded[loaded.module_root]

    # Typed readback
    assert node.metadata[HugrGenerator] == gen
    assert node.metadata.get(HugrGenerator) == gen
    assert node.metadata[HugrUsedExtensions] == exts
    assert node.metadata.get(HugrUsedExtensions) == exts

    # Check the raw JSON encoding
    raw = node.metadata.as_dict()
    assert raw[HugrGenerator.KEY] == {"name": "hugr-py-test", "version": "1.2.3"}
    assert raw[HugrUsedExtensions.KEY] == [
        {"name": "ext.a", "version": "0.1.0"},
        {"name": "ext.b", "version": "2.0.0"},
    ]


def test_metadata_default() -> None:
    hugr = Hugr[Any]()
    node = hugr[hugr.module_root]

    assert node.metadata.get(HugrGenerator) is None
    assert node.metadata.get(
        HugrGenerator, GeneratorDesc("hugr-py-test", Version.parse("1.2.3"))
    ) == GeneratorDesc("hugr-py-test", Version.parse("1.2.3"))
