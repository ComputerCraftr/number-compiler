"""Independent decimal tests for the ×5 low-column CF operator."""

from __future__ import annotations

from random import Random

import pytest

from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.sequences.antihydra.mahler_cf_low_period import (
    low_suffix_response,
)


def literal_action(exponent: int, columns: int) -> Matrix2:
    value = int.__pow__(5, exponent, 10**columns)
    result = Matrix2.identity()
    for digit in f"{value:0{columns}d}":
        result = result.multiply(Matrix2.digit(int(digit) + 1))
    return result


def test_low_suffix_is_ordered_physical_decimal_source() -> None:
    rng = Random(9037)
    for columns in range(1, 17):
        for exponent in (columns, columns + 1, 64, 128, 514):
            if exponent >= columns:
                assert low_suffix_response(
                    exponent, columns, reserve_bits=lambda _: None
                ) == literal_action(exponent, columns)
        for _ in range(40):
            exponent = rng.randrange(columns, 1024)
            assert low_suffix_response(
                exponent, columns, reserve_bits=lambda _: None
            ) == literal_action(exponent, columns)


def test_settled_phase_reduction_with_large_exponent() -> None:
    for columns in range(1, 17):
        period = 1 if columns <= 2 else 1 << (columns - 2)
        start = columns + period + 3
        expected = low_suffix_response(start, columns, reserve_bits=lambda _: None)
        assert (
            low_suffix_response(
                start + period * 10**90, columns, reserve_bits=lambda _: None
            )
            == expected
        )


def test_unsettled_suffix_and_reservation_refusal() -> None:
    with pytest.raises(ValueError):
        low_suffix_response(3, 4, reserve_bits=lambda _: None)
    with pytest.raises(ValueError):
        low_suffix_response(20, 17, reserve_bits=lambda _: None)

    def refuse(_bits: int) -> None:
        raise MemoryError("low-column scratch refused")

    with pytest.raises(MemoryError, match="scratch refused"):
        low_suffix_response(4096, 16, reserve_bits=refuse)


def test_settled_phase_returns_the_shared_complete_operator() -> None:
    from number_compiler.sequences.antihydra.mahler_cf_low_period import (
        settled_low_action,
    )

    assert settled_low_action(3, 2) is settled_low_action(4, 2)
    assert settled_low_action(3, 3) != settled_low_action(4, 3)
    for width in range(1, 5):
        period = 1 << max(width - 2, 0)
        phases = [settled_low_action(width + i, width) for i in range(period)]
        assert len(set(phases)) == period
        for phase, response in enumerate(phases):
            assert response == literal_action(width + phase, width).entries
            assert settled_low_action(width + phase + period, width) is response
    with pytest.raises(ValueError, match="unsettled"):
        settled_low_action(3, 4)


def test_exact_suffix_context_and_modular_precision_controls() -> None:
    from number_compiler.sequences.antihydra.mahler_cf_low_period import (
        settled_low_action,
    )

    first = settled_low_action(8, 4)
    later = settled_low_action(10, 4)
    values = tuple(a + 3 * b for a, b, _, _ in (first, later))
    assert values == (233, 1258)
    assert values[0] % 25 == values[1] % 25
    assert values[0] % 125 != values[1] % 125

    first = settled_low_action(3, 3)
    later = settled_low_action(4, 3)
    assert first[2:] == later[2:] == (19, 3)
    # Weights (2, -11) annihilate the raw-digit row (11, 2).
    assert tuple((2 * a - 11 * b) % 125 for a, b, _, _ in (first, later)) == (11, 36)
    prefix = Matrix2.digit(2)
    early_row = prefix.multiply(Matrix2(first)).entries[2:]
    late_row = prefix.multiply(Matrix2(later)).entries[2:]
    assert early_row == (44, 7)
    assert late_row == (139, 22)
    assert early_row[0] % 25 != late_row[0] % 25


@pytest.mark.parametrize("modulus", [2, 5, 10, 25, 125])
def test_complete_modular_action_period(modulus: int) -> None:
    def reserve(_bits: int) -> None:
        pass

    for width in range(3, 10):
        period = 1 << (width - 2)
        expected = period // 2 if modulus == 5 else period
        rows = [
            Matrix2(
                low_suffix_response(n, width, reserve_bits=reserve).entries, modulus
            )
            for n in range(width, width + 2 * period)
        ]
        assert rows[:period] == rows[expected : expected + period]
        if expected > 1:
            shorter = expected // 2
            assert rows[:period] != rows[shorter : shorter + period]
