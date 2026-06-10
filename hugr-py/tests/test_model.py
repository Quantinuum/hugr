from semver import Version

from hugr import model


def test_symbol_version_text():
    symbol = model.Symbol.from_str("public ext.op@0.2.3 (core.fn [] [])")

    assert symbol.name == "ext.op"
    assert symbol.version == Version.parse("0.2.3")
    assert str(symbol) == "public ext.op@0.2.3 (core.fn [] [])"


def test_import_version_text():
    package = model.Package.from_str("(hugr 0)\n\n(mod)\n\n(import ext.op@0.2.3)")

    operation = package.modules[0].root.children[0].operation
    assert operation == model.Import("ext.op", Version.parse("0.2.3"))
    assert "(import ext.op@0.2.3)" in str(package)


def test_symbol_escaped_name_text_roundtrip():
    name = "tests.integration.test_basic.test_implicit_return.<locals>.ret"
    sig = model.Apply("core.fn", [model.List([]), model.List([])])
    symbol = model.Symbol(name, "Public", signature=sig)

    text = str(symbol)
    parsed = model.Symbol.from_str(text)

    assert f'"{name}"' in text
    assert parsed == symbol


def test_package_escaped_name_text_roundtrip():
    name = "tests.integration.test_basic.test_implicit_return.<locals>.ret"
    source = f"""(hugr 0)

(mod)

(import core.fn)

(declare-func public "{name}" (core.fn [] []))
"""

    text = str(model.Package.from_str(source))
    parsed = model.Package.from_str(text)

    assert f'"{name}"' in text
    assert str(parsed) == text
