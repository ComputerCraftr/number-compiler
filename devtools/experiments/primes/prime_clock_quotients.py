"""Exact recursive prime-clock wheel quotient audit.

This module contains only the positive prime-wheel result from v0.42.  The
reverse-add/Collatz carry-shadow experiments were removed in v0.43 after the
radial/innovation decomposition made them obsolete.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from math import gcd

from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.sequences.prime.wheel_cyclotomic import (
    PrimeWheelPhaseBlock,
    extend_prime_wheel_gaps,
)


@dataclass(frozen=True, slots=True)
class PrimeClockWheelStageAudit:
    old_modulus: int
    new_prime: int
    old_gap_states: int
    new_gap_states: int
    alpha: int
    phase_shift: int
    phase_itinerary_bits: int
    raw_histogram_bits: int
    circular_quotient_bits: int
    max_histogram_deviation: int
    endpoint_difference_exact: bool
    half_gap_radix_exact: bool
    q_power_phase_identity: bool
    q_power_histogram_uniform: bool
    first_gap_recurrence_exact: bool
    extension_exact: bool


def _direct_wheel_gaps(modulus: int) -> tuple[int, ...]:
    M = int(modulus)
    residues = [value for value in range(1, M + 1) if gcd(value, M) == 1]
    return tuple(
        residues[(i + 1) % len(residues)]
        + (M if i + 1 == len(residues) else 0)
        - residues[i]
        for i in range(len(residues))
    )


def prime_clock_wheel_audits() -> tuple[PrimeClockWheelStageAudit, ...]:
    stages: list[PrimeClockWheelStageAudit] = []
    modulus = 2
    gaps: tuple[int, ...] = (2,)
    for q in (3, 5, 7, 11, 13, 17):
        new, block, _initial = extend_prime_wheel_gaps(
            gaps, old_modulus=modulus, new_prime=q
        )
        histogram = block.circular.histogram()
        raw_histogram_bits = sum(bit_width(value) for value in histogram)
        phase_itinerary_bits = len(gaps) * bit_width(q - 1)
        linear_differences = tuple(gaps[i + 1] - gaps[i] for i in range(len(gaps) - 1))
        by_difference = PrimeWheelPhaseBlock.from_endpoint_differences(
            gaps[0],
            linear_differences,
            prime=q,
            alpha=block.alpha,
        )
        half = tuple(gap // 2 for gap in gaps)
        half_block = PrimeWheelPhaseBlock.from_gaps(
            half,
            prime=q,
            alpha=(2 * block.alpha) % q,
        )
        powered = block.power_block(q)
        powered_histogram = powered.circular.histogram()
        direct = _direct_wheel_gaps(modulus * q)
        stages.append(
            PrimeClockWheelStageAudit(
                modulus,
                q,
                len(gaps),
                len(new),
                block.alpha,
                block.phase_shift,
                phase_itinerary_bits,
                raw_histogram_bits,
                block.circular.description_bits,
                block.circular.max_deviation,
                by_difference.canonical_key == block.canonical_key,
                (
                    half_block.length == block.length
                    and half_block.phase_shift == block.phase_shift
                    and half_block.circular == block.circular
                ),
                powered.phase_shift == 0,
                len(set(powered_histogram)) == 1 and powered_histogram[0] == len(gaps),
                len(gaps) == 1 or new[0] == gaps[0] + gaps[1],
                new == direct,
            )
        )
        modulus *= q
        gaps = new
    return tuple(stages)


def metrics_as_jsonable(
    rows: tuple[PrimeClockWheelStageAudit, ...],
) -> dict[str, object]:
    return {"prime": [asdict(row) for row in rows]}
