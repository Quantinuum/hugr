# /// script
# requires-python = ">=3.13"
# dependencies = [
#     "guppylang ==0.21.6",
# ]
# ///
"""An function with a Rz operation"""

from pathlib import Path
from sys import argv

from guppylang import guppy
from guppylang.std.angles import angle
from guppylang.std.builtins import owned
from guppylang.std.quantum import qubit, rz


@guppy
def one_rz(q0: qubit @ owned, angle: angle) -> qubit:
    rz(q0, angle)
    return q0


program = one_rz.compile_function()
Path(argv[0]).with_suffix(".hugr").write_bytes(program.to_bytes())
