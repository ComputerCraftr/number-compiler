"""Shared affine and Frobenius arithmetic for source-bound transports."""

from __future__ import annotations

from collections.abc import Callable
from typing import TypeVar

T = TypeVar("T")


def radix_exponent_factors(exponent: int, radix: int) -> tuple[tuple[int, int], ...]:
    """Factor a nonnegative exponent into its nonzero radix powers.

    A pair ``(stride, multiplicity)`` denotes the corresponding Frobenius
    factor. Callers own the field law and decide whether that factor survives.
    """
    if type(exponent) is not int or exponent < 0:
        raise ValueError("Frobenius exponent must be a nonnegative exact integer")
    if type(radix) is not int or radix < 2:
        raise ValueError("Frobenius radix must be an exact integer at least two")
    factors: list[tuple[int, int]] = []
    stride = 1
    while exponent:
        exponent, multiplicity = divmod(exponent, radix)
        if multiplicity:
            factors.append((stride, multiplicity))
        stride *= radix
    return tuple(factors)


def apply_output_forcing(
    source: T,
    forcing: T,
    *,
    apply_linear: Callable[[T], T],
    add: Callable[[T, T], T],
) -> T:
    """Return ``A*source + forcing`` in one caller-aligned value space."""
    return add(apply_linear(source), forcing)


def compose_output_forcing(
    earlier: T,
    later: T,
    *,
    apply_later_linear: Callable[[T], T],
    add: Callable[[T, T], T],
) -> T:
    """Return the affine composite forcing ``A_later*earlier + later``."""
    return apply_output_forcing(
        earlier,
        later,
        apply_linear=apply_later_linear,
        add=add,
    )


__all__ = [
    "apply_output_forcing",
    "compose_output_forcing",
    "radix_exponent_factors",
]
