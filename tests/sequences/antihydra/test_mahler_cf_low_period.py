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
