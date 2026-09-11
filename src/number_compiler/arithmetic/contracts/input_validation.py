"""Exact integer admission shared by public inputs and resource boundaries."""

from __future__ import annotations


def require_integer(
    value: object, name: str, minimum: int | None = None, maximum: int | None = None
) -> int:
    """Reject coercions that alias distinct requests before doing any work."""
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer")
    if (
        minimum is not None
        and value < minimum
        or maximum is not None
        and value > maximum
    ):
        if minimum is None:
            bound = f"<= {maximum}"
        elif maximum is None:
            bound = f">= {minimum}"
        else:
            bound = f"between {minimum} and {maximum}"
        raise ValueError(f"{name} must be {bound}")
    return value


__all__ = ["require_integer"]
