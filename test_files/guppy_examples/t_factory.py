# /// script
# requires-python = ">=3.13"
# dependencies = [
#     "guppylang==1.0.0a5",
#     "guppylang-internals==1.0.0a5",
# ]
# ///
"""A small T-state factory using magic-state distillation."""

from pathlib import Path
from sys import argv

from guppylang import guppy
from guppylang.std.angles import angle, pi
from guppylang.std.builtins import array, owned, py
from guppylang.std.option import Option, nothing, some
from guppylang.std.quantum import cz, discard, h, measure, qubit, ry, rz

PHI = 1.2309594173407747  # acos(1 / 3)
ATTEMPTS = 3


@guppy
def prepare_approx() -> qubit:
    q = qubit()
    ry(q, angle(py(PHI)))
    rz(q, pi / 4)
    return q


@guppy
def distill(
    target: qubit @ owned,
    qs: array[qubit, 4] @ owned,
) -> tuple[qubit, bool]:
    cz(qs[0], qs[1])
    cz(qs[2], qs[3])
    cz(target, qs[0])
    cz(qs[1], qs[2])
    cz(target, qs[3])

    for i in range(4):
        h(qs[i])
    bits = array(not measure(q) for q in qs)

    success = True
    for b in bits:
        success &= b
    return target, success


@guppy
def t_state(attempts: int) -> Option[qubit]:
    if attempts > 0:
        target = prepare_approx()
        ancillae = array(prepare_approx() for _ in range(4))

        q, success = distill(target, ancillae)
        if success:
            return some(q)

        discard(q)
        return t_state(attempts - 1)

    return nothing()


@guppy
def main() -> None:
    option_t = t_state(ATTEMPTS)
    if option_t.is_some():
        discard(option_t.unwrap())
    else:
        option_t.unwrap_nothing()


program = main.compile_function()
Path(argv[0]).with_suffix(".hugr").write_bytes(program.to_bytes())
