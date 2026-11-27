"""Explicit admission switch for bounded optional native reversal actions."""

import os


def native_reverse_enabled() -> bool:
    """Return whether the query opted into bounded native reversal actions."""
    return os.environ.get("NUMBER_COMPILER_ENABLE_NATIVE_REVERSE") == "1"
