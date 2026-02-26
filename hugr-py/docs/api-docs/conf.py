# Configuration file for the Sphinx documentation builder.  # noqa: INP001
# See https://www.sphinx-doc.org/en/master/usage/configuration.html
import hugr

project = "HUGR Python"
copyright = "2025, Quantinuum"
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
]

# HTML configs
html_theme = "furo"
html_title = f"HUGR-py v{hugr.__version__} documentation."
html_theme_options = {
    "sidebar_hide_name": False,
}
html_static_path = ["../_static"]
html_logo = "../_static/hugr_logo_no_bg.svg"
html_show_sourcelink = False

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
