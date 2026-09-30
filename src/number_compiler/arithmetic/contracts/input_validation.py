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


def normalized_integer_pair(
    first: int, second: int, *, first_minimum: int = 0, second_minimum: int = 0
) -> tuple[int, int]:
    """Preserve legacy algebraic integer coercion and paired range diagnostics."""
    left, right = int(first), int(second)
    if left < first_minimum or right < second_minimum:
        raise ValueError((left, right))
    return left, right


__all__ = ["require_integer"]


def normalized_odd_modulus(value: int, *, minimum: int = 3) -> int:
    """Admit legacy integer-coercing odd ring moduli with scalar diagnostics."""
    modulus = int(value)
    if modulus < minimum or not (modulus & 1):
        raise ValueError(modulus)
    return modulus
