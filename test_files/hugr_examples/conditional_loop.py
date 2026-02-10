# /// script
# requires-python = ">=3.13"
# dependencies = [
#     "guppylang ==0.21.6",
# ]
# ///
"""A loop inside a conditional branch"""

from pathlib import Path
from sys import argv

from guppylang import guppy
from guppylang.std.angles import angle
from guppylang.std.builtins import owned
from guppylang.std.quantum import qubit, h, rz


@guppy
def conditional_loop(q0: qubit @ owned, angle: angle, n: int, cond: bool) -> qubit:
    if cond:
        while n > 0:
            h(q0)
            n = n - 1
    else:
        rz(q0, angle)
    return q0


program = conditional_loop.compile_function()
Path(argv[0]).with_suffix(".hugr").write_bytes(program.to_bytes())
