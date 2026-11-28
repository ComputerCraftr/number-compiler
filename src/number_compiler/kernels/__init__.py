"""Lazy admission helpers for optional bounded native actions."""

import os
from functools import cache
from importlib import import_module
from types import ModuleType


def native_reverse_enabled() -> bool:
    """Return whether the query opted into bounded native reversal actions."""
    return os.environ.get("NUMBER_COMPILER_ENABLE_NATIVE_REVERSE") == "1"


@cache
def native_continuant_module() -> ModuleType | None:
    """Load the optional arithmetic extension only for a demanded action."""
    name = "number_compiler.kernels._cf_continuant"
    try:
        return import_module(name)
    except ModuleNotFoundError as error:
        if error.name != name:
            raise
        return None
