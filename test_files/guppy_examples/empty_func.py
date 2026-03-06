# /// script
# requires-python = ">=3.13"
# dependencies = [
#     "guppylang ==0.21.6",
# ]
# ///
"""An empty function returning an int"""

from pathlib import Path
from sys import argv

from guppylang import guppy


@guppy
def empty_func() -> int:
    return 1


program = empty_func.compile_function()
Path(argv[0]).with_suffix(".hugr").write_bytes(program.to_bytes())
