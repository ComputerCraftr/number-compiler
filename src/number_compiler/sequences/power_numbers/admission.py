"""Bounded theorem admission for symbolic Fermat/Mersenne candidates."""

from __future__ import annotations

from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent


def require_special_candidate_budget(
    family: str,
    parameter: int,
    max_candidate_bits: int = 1_000_000,
) -> int | DyadicExtent:
    """Return the symbolic candidate width after checking an explicit bit cap."""
    if type(family) is not str or family not in ("fermat", "mersenne"):
        raise ValueError(family)
    if type(parameter) is not int or parameter < 0:
        raise ValueError("special parameter must be a nonnegative exact integer")
    if family == "mersenne" and parameter < 2:
        raise ValueError(parameter)
    if type(max_candidate_bits) is not int or max_candidate_bits < 1:
        raise ValueError("max_candidate_bits must be a positive exact integer")
    bits: int | DyadicExtent = (
        DyadicExtent(parameter, 1) if family == "fermat" else parameter
    )
    if bits > max_candidate_bits:
        raise ValueError("candidate exceeds max_candidate_bits")
    return bits


__all__ = ["require_special_candidate_budget"]
