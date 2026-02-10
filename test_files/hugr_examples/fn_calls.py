# /// script
# requires-python = ">=3.13"
# dependencies = [
#     "guppylang ==0.21.6",
# ]
# ///
"""Nested function calls"""

from pathlib import Path
from sys import argv

from guppylang import guppy
from guppylang.std.angles import angle
from guppylang.std.builtins import owned
from guppylang.std.quantum import qubit, h, rz


@guppy
def inner(q0: qubit @ owned, angle: angle) -> qubit:
    rz(q0, angle)
    return q0


@guppy
def mid(q0: qubit @ owned) -> qubit:
    a = angle(3.14)
    return inner(q0, a)


@guppy
def outer(q0: qubit @ owned) -> qubit:
    h(q0)
    return mid(q0)


program = inner.compile_function()
Path(argv[0]).with_suffix(".hugr").write_bytes(program.to_bytes())
