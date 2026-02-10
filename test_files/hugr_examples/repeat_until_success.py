# /// script
# requires-python = ">=3.13"
# dependencies = [
#     "guppylang >=0.21.6",
# ]
# ///
"""An RUS program"""

from pathlib import Path
from sys import argv

from guppylang import guppy
from guppylang.std.builtins import result
from guppylang.std.quantum import qubit, cx, discard, h, measure, t, tdg, z


@guppy
def repeat_until_success(q: qubit) -> None:
    attempts = 0
    while True:
        attempts += 1

        a, b = qubit(), qubit()
        h(a)
        h(b)

        tdg(a)
        cx(b, a)
        t(a)
        h(a)
        if measure(a):
            discard(b)
            continue

        t(q)
        z(q)
        cx(q, b)
        t(b)
        h(b)
        if measure(b):
            z(q)
            continue

        result("attempts", attempts)
        break


program = repeat_until_success.compile_function()
Path(argv[0]).with_suffix(".hugr").write_bytes(program.to_bytes())
