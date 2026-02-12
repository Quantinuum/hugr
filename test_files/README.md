
# Test HUGR programs

This directory contains test HUGR files with their source scripts.

## Folders

- `guppy_examples/`  
  Guppy source examples written as `.py` [uv script](https://docs.astral.sh/uv/guides/scripts/). Each script defines a test program for a pinned version of guppylang. The compiled HUGR is stored alongside it with a `.hugr` extension. The guppylang version used is defined by each script.

- `hugr_examples/`  
  Python scripts that generate HUGR directly (not via guppylang).  
  The produced `.hugr` are in the same folder.

## Commands

From this directory, use:

- `just recompile`  
  Re-generate all `.hugr` files.

- `just clean-hugrs`  
  Remove all `.hugr` files recursively.

- `just clean-hugrs-interactive`  
  Show files to be deleted and ask for confirmation.

