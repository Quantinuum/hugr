"""Types and operations from the standard extension set."""

from hugr.ext import Extension, ExtensionRegistry

from . import collections, float, int, logic, prelude, ptr

__all__ = ["PRELUDE", "collections", "float", "int", "logic", "prelude", "ptr"]

PRELUDE: Extension = prelude.PRELUDE_EXTENSION


def _std_extensions() -> ExtensionRegistry:
    return ExtensionRegistry.from_extensions(
        [
            PRELUDE,
            int.CONVERSIONS_EXTENSION,
            int.INT_TYPES_EXTENSION,
            int.INT_OPS_EXTENSION,
            float.FLOAT_OPS_EXTENSION,
            float.FLOAT_TYPES_EXTENSION,
            logic.EXTENSION,
            ptr.EXTENSION,
            collections.array.EXTENSION,
            collections.borrow_array.EXTENSION,
            collections.list.EXTENSION,
            collections.static_array.EXTENSION,
        ]
    )
