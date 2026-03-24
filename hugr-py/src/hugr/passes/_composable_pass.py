"""A Protocol for a composable pass.

Deprecated module alias for `hugr.passes.composable`.
"""

from .composable import (
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
