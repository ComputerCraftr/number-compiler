"""Shared output-forcing algebra for source-bound affine transports."""

from __future__ import annotations

from collections.abc import Callable
from typing import TypeVar

T = TypeVar("T")


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


__all__ = ["apply_output_forcing", "compose_output_forcing"]
