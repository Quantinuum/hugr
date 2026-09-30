"""Check the generated pointer extension used by Python."""

import pytest

from hugr import tys
from hugr.std import ptr


@pytest.mark.parametrize("element", [tys.Bool, tys.Qubit])
def test_pointer_is_linear(element: tys.Type) -> None:
    assert ptr.Ptr(element).type_bound() == tys.TypeBound.Linear


def test_pointer_operations() -> None:
    assert set(ptr.EXTENSION.operations) == {
        "New",
        "Read",
        "Write",
        "Swap",
        "Dup",
        "Free",
        "Map",
    }
