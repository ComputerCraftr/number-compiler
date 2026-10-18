"""Typed handle to exact integer power when a test patches builtins.pow."""

from __future__ import annotations


def exact_integer_power(base: int, exponent: int, modulus: int | None = None) -> int:
    """Call the integer implementation directly, bypassing patched builtins.pow."""
    if modulus is None:
        return int(base.__pow__(exponent))
    return int(base.__pow__(exponent, modulus))
