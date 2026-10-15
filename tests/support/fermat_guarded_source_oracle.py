"""Small literal references for guarded binary-source unit tests only."""

from __future__ import annotations

from collections.abc import Sequence

from number_compiler.sequences.power_numbers.three_power_pumped_fold import (
    GuardedXorRun,
)


def literal_toggle_runs(
    source_bits: Sequence[int], runs: Sequence[GuardedXorRun]
) -> tuple[int, ...]:
    bits = list(source_bits)
    for run in runs:
        segment = bits[run.start : run.end]
        if len(segment) != run.length or any(
            bit != run.expected_bit for bit in segment
        ):
            raise ValueError("literal source guard failed")
        bits[run.start : run.end] = [1 - bit for bit in segment]
    return tuple(bits)


def literal_fermat_residue(bits: Sequence[int], width: int) -> int:
    value = sum(bit << position for position, bit in enumerate(bits))
    return value % ((1 << width) + 1)


def literal_radial_width(bits: Sequence[int]) -> tuple[int, int, int]:
    value = sum(bit << position for position, bit in enumerate(bits))
    if value <= 0:
        raise ValueError("radial oracle expects a positive source")
    source_bits = value.bit_length()
    threshold = ((1 << (source_bits + 1)) + 2) // 3
    comparison = (value > threshold) - (value < threshold)
    return source_bits, comparison, (3 * value).bit_length()


def literal_pivot_packet(level: int, offsets: tuple[int, ...]) -> tuple[object, ...]:
    source = 3 ** (1 << level)
    following = source * source
    later = following * following
    pivot = level + 2
    precision = max(offsets) + 1
    unit = (source - 1) >> pivot
    next_unit = (following - 1) >> (pivot + 1)
    source_bits: list[int] = []
    tripling: list[int] = []
    innovation: list[int] = []
    successive: list[int] = []
    for offset in range(max(offsets) + 1):
        column = pivot + offset
        source_bits.append((source >> column) & 1)
        lower_modulus = 1 << (column + 1)
        tripling.append((3 * (source % lower_modulus)) >> (column + 1))
        innovation.append(int(following % lower_modulus < source % lower_modulus))
        old_innovation = following - source
        new_innovation = later - following
        successive.append(
            int(new_innovation % lower_modulus < old_innovation % lower_modulus)
        )

    def select(values: list[int]) -> tuple[int, ...]:
        return tuple(values[offset] for offset in offsets)

    return (
        select(source_bits),
        select(tripling),
        select(innovation),
        select(successive),
        (unit ^ next_unit) & ((1 << precision) - 1),
    )


def literal_unit_window(level: int, width: int, offset: int = 0) -> tuple[int, int]:
    precision = offset + width
    # The following normalized unit divides by one additional power of two,
    # so preserve one extra source bit before taking that quotient.
    modulus = 1 << (level + 3 + precision)
    source = pow(3, 1 << level, modulus)
    next_source = source * source % modulus
    unit = (source - 1) >> (level + 2)
    next_unit = (next_source - 1) >> (level + 3)
    mask = (1 << width) - 1
    return (unit >> offset) & mask, (next_unit >> offset) & mask


__all__ = [
    "literal_fermat_residue",
    "literal_pivot_packet",
    "literal_radial_width",
    "literal_toggle_runs",
    "literal_unit_window",
]
