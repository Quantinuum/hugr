"""A Protocol for a composable pass.

Deprecated module alias for `hugr.passes.composable_pass`.
"""

from .composable_pass import (
    ComposablePass,
    ComposedPass,
    PassName,
    PassResult,
    implement_pass_run,
)

__all__ = [
    "PassName",
    "PassResult",
    "ComposedPass",
    "ComposablePass",
    "implement_pass_run",
]
