# Configuration file for the Sphinx documentation builder.  # noqa: INP001
# See https://www.sphinx-doc.org/en/master/usage/configuration.html
from datetime import datetime
from pathlib import Path

import hugr

project = "HUGR"
copyright = f"{datetime.now().year}, Quantinuum"
author = "Quantinuum"

extensions = [
    "sphinx.ext.napoleon",
    "sphinx.ext.autodoc",
    "sphinx.ext.coverage",
    "sphinx.ext.autosummary",
    "sphinx.ext.viewcode",
    "sphinx.ext.intersphinx",
    "myst_parser",
    "sphinxcontrib.mermaid",
    "sphinx_favicon",
]

# HTML configs
html_theme = "furo"
html_title = "HUGR documentation"
html_theme_options = {
    "sidebar_hide_name": False,
}
html_static_path = ["../_static"]
html_logo = "../_static/hugr_logo.svg"
html_show_sourcelink = False
favicons = [{"href": "hugr_logo_no_bg.svg"}]

# General sphinx configs
autosummary_generate = True
templates_path = ["_templates"]
exclude_patterns = [
    "_build",
    "Thumbs.db",
    ".DS_Store",
    "conftest.py",
    # Included inside the index
    "specification/motivation.md",
]

# Support markdown files for the specification docs.
myst_enable_extensions = [
    "html_image",
    "colon_fence",
    "dollarmath",
    "amsmath",
    "attrs_inline",
]
myst_fence_as_directive = ["mermaid"]

# Mermaid configs
#
# This doesn't actually work, the theme is still set to default :/
# See https://github.com/mgaitan/sphinxcontrib-mermaid/issues/39
mermaid_params = ["--theme", "dark", "--backgroundColor", "transparent"]

intersphinx_mapping = {
    "python": ("https://docs.python.org/3/", None),
}


# -----------------------------------------------------------------------------
# Custom variables used in the rendered documents.
# -----------------------------------------------------------------------------


def _read_hugr_rs_version() -> str:
    """Read the hugr crate version from hugr/Cargo.toml."""
    try:
        # Note: `tomllib` is only available in Python 3.11 and later.
        #
        # Docs are generated with Python 3.14, but we catch the ImportError
        # here to avoid breaking the tests.
        import tomllib  # type: ignore[import-not-found]
    except ModuleNotFoundError:
        return " unknown"
    cargo_toml = Path(__file__).resolve().parents[3] / "hugr" / "Cargo.toml"
    with cargo_toml.open("rb") as f:
        data = tomllib.load(f)
    return data["package"]["version"]


hugr_py_version = hugr.__version__
hugr_rs_version = _read_hugr_rs_version()

rst_epilog = f"""
.. |hugr_py_version| replace:: {hugr_py_version}
.. |hugr_rs_version| replace:: {hugr_rs_version}
"""
