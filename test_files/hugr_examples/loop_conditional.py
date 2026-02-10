# /// script
# requires-python = ">=3.13"
# dependencies = [
#     "guppylang ==0.21.6",
# ]
# ///
"""A conditional branch inside a loop"""

from pathlib import Path
from sys import argv

from guppylang import guppy
from guppylang.std.angles import angle
from guppylang.std.builtins import owned
from guppylang.std.quantum import qubit, h, rz


@guppy
def loop_conditional(q0: qubit @ owned, angle: angle, n: int, cond: bool) -> qubit:
    while n > 0:
        if cond:
            h(q0)
        else:
            rz(q0, angle)
        n = n - 1
    return q0


program = loop_conditional.compile_function()
Path(argv[0]).with_suffix(".hugr").write_bytes(program.to_bytes())
