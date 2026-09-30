from pathlib import Path

from hugr.package import Package

guppyft_steane = (
    Path(__file__).parent.parent.parent.parent / "resources/test/guppyft-steane.hugr"
)


def test_guppyft_steane_serialise(benchmark) -> None:
    pkg = Package.from_bytes(guppyft_steane.read_bytes())

    def guppyft_steane_serialise() -> None:
        pkg.to_bytes()

    benchmark(guppyft_steane_serialise)


def test_guppyft_steane_deserialise(benchmark) -> None:
    pkg_bytes = guppyft_steane.read_bytes()

    def guppyft_steane_deserialise() -> None:
        Package.from_bytes(pkg_bytes)

    benchmark(guppyft_steane_deserialise)
