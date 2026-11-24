"""Independent literal guard and ordered-word oracle for finite CF cylinders."""

from __future__ import annotations

from fractions import Fraction
from itertools import product

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.mahler_continued_fraction_cylinder import (
    continued_fraction_cylinder,
)


def literal_guarded_cylinder(horizon: int, budget: int) -> dict[str, object]:
    """Refine one decimal coefficient and execute one physical step at a time."""
    q, r, p, s = 1, 0, 0, 1
    count = extent = innovation = 0
    gain = modulus = 1
    exponent = 1
    row = iter(str(5))
    while True:
        if count:
            lower, upper = sorted((Fraction(p, q), Fraction(p + s, q + r)))
            current_lower = (gain * lower - innovation) / modulus
            current_upper = (gain * upper - innovation) / modulus
            safe = 0 <= current_lower < current_upper <= Fraction(1, 2)
            if safe and extent == horizon:
                break
            if safe and current_upper <= Fraction(1, 3):
                innovation *= 3
                gain *= 3
                modulus *= 2
                extent += 1
                continue
            if safe and current_lower >= Fraction(1, 3):
                innovation = innovation * 3 + modulus
                gain *= 3
                modulus *= 2
                extent += 1
                continue
        if count >= budget:
            return {
                "status": "unknown",
                "reason": "continued-fraction coefficient budget exhausted",
                "source_law": "decimal-powers-of-five",
                "coefficient_count": count,
                "certified_physical_ticks": extent,
            }
        try:
            digit = next(row)
        except StopIteration:
            exponent += 1
            row = iter(str(5**exponent))
            digit = next(row)
        coefficient = int(digit) + 1
        q, r, p, s = q * coefficient + r, q, p * coefficient + s, p
        count += 1
    return {
        "status": "available",
        "source_law": "decimal-powers-of-five",
        "clock_unit": "physical-recurrence-ticks",
        "horizon": horizon,
        "coefficient_count": count,
        "matrix": ((q, r), (p, s)),
        "fraction_lower": {
            "numerator": lower.numerator,
            "denominator": lower.denominator,
        },
        "fraction_upper": {
            "numerator": upper.numerator,
            "denominator": upper.denominator,
        },
        "endpoint_lower": {
            "numerator": current_lower.numerator,
            "denominator": current_lower.denominator,
        },
        "endpoint_upper": {
            "numerator": current_upper.numerator,
            "denominator": current_upper.denominator,
        },
        "source_residue": (-innovation * pow(gain, -1, modulus)) % modulus,
        "source_modulus": modulus,
        "weighted_innovation": innovation,
        "authority_scope": "bounded-cf-fractional-cylinder",
    }


@pytest.mark.parametrize(
    ("horizon", "budget"),
    [
        *product((0, 1, 2, 3, 8, 15, 20, 63, 96, 256, 512), (1, 2, 3, 7, 31, 64, 600)),
        *product((1024, 2048, 3072), (64, 600)),
        *product((4096,), (32, 64, 539, 540)),
    ],
)
def test_literal_exact_partial_clock_and_packet(horizon: int, budget: int) -> None:
    expected = literal_guarded_cylinder(horizon, budget)
    ledger = ResourceLedger(max_nodes=10_000)
    actual = continued_fraction_cylinder(horizon, budget, ledger=ledger)
    assert actual == expected
    assert ledger.nodes == ledger.entries == 0
