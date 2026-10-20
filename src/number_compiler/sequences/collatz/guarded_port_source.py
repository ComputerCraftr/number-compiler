"""Canonical pullbacks from temporal guards to original Collatz cylinders."""

from __future__ import annotations

from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.guarded_radix6_bridge import FiveBand
from number_compiler.sequences.collatz.source_closed_port_action import (
    SourceCongruence,
)


def ceil_div(numerator: int, denominator: int) -> int:
    """Exact ceiling quotient used to intersect half-open integer bounds."""
    return -((-numerator) // denominator)


def restrict_source(
    inlet: CollatzTwoSidedCylinder,
    guard: SourceCongruence,
) -> CollatzTwoSidedCylinder | None:
    """Intersect a CRT guard and its minimum-positive-source boundary."""
    result = inlet.intersect_congruence(guard.residue, guard.modulus)
    if result is not None and result.first < guard.minimum_source:
        result = result.intersect_interval(guard.minimum_source, result.upper)
    return result


def restrict_forced_five_suffix(
    inlet: CollatzTwoSidedCylinder,
    prefix: DyadicTerminalFieldAction,
    band: FiveBand,
) -> CollatzTwoSidedCylinder | None:
    """Pull one authenticated low base-6 suffix back to its root cylinder."""
    if band.lower != 0:
        raise ValueError("source suffix restriction requires a low five band")
    modulus = 6**band.upper
    guard = SourceCongruence(modulus - 1, modulus).pullback(prefix)
    return None if guard is None else restrict_source(inlet, guard)


def merge_five_source_bands(
    *band_sets: tuple[FiveBand, ...],
) -> tuple[FiveBand, ...]:
    """Union authenticated base-6 bands while preserving all intervals."""
    from number_compiler.sequences.collatz.guarded_radix6_bridge import merge_bands

    return merge_bands(tuple(band for bands in band_sets for band in bands))


__all__ = [
    "ceil_div",
    "merge_five_source_bands",
    "restrict_forced_five_suffix",
    "restrict_source",
]
