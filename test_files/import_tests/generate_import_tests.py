#!/usr/bin/env python
"""Generates the HUGR files used by the Rust HUGR import integration tests.

usage: python generate_import_tests.py
"""
from pathlib import Path
from typing import Callable

from hugr import val
from hugr.build import Module
from hugr.package import Package


def case_entry_block_part_of_loop() -> bytes:
    mb = Module()
    main = mb.define_main(input_types=[])
    cfg = main.add_cfg()

    with cfg.add_entry() as entry:
        branching = entry.load(val.TRUE)
        entry.set_block_outputs(branching)
    cfg.branch_exit(entry[0])
    with cfg.add_successor(entry[1]) as b:
        b.set_single_succ_outputs(*b.inputs())
    cfg.branch(b[0], entry)

    main.set_outputs()

    return Package([mb.hugr], extensions=[]).to_bytes()


cases: list[Callable[[], bytes]] = [
    case_entry_block_part_of_loop
]

if __name__ == "__main__":
    print("Generating HUGR import test files...")
    file_dir = Path(__file__).parent
    for case in cases:
        file_dir.mkdir(parents=True, exist_ok=True)
        with (file_dir / f"{case.__name__}.hugr").open("wb") as f:
            f.write(case())
    print("Done with generating HUGR import test files!")
