# Guppy-generated test programs

This directory contains simple guppy program definitions used for testing.

Each example is defined as a `.py` [uv script](https://docs.astral.sh/uv/guides/scripts/)
that defines the guppy program for a pinned version of guppylang.
The compiled HUGR is stored alongside it with a `.hugr` extension.

Run `just recompile` in this directory (or `just recompile-test-hugrs` on
the root) to recompile the `.hugr` files.
The guppylang version used is defined by each script.
