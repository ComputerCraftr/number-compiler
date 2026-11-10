"""Source-independent finite decimal word and cyclotomic coordinate laws."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.automata.decimal_mod70_word import (
    DecimalMod70WordSummary,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
    crt_mod70_from_residues,
    phi6_coefficients_from_root_values_mod7,
)
from tests.support.decimal_mod70_oracle import (
    literal_mod70_packet as _literal_mod70_packet,
)


def test_phi6_root_interpolation_and_mod70_crt_are_exact_coordinates() -> None:
    for coefficient_zero in range(7):
        for coefficient_one in range(7):
            at_three = (coefficient_zero + 3 * coefficient_one) % 7
            at_five = (coefficient_zero + 5 * coefficient_one) % 7
            assert phi6_coefficients_from_root_values_mod7(at_three, at_five) == (
                coefficient_zero,
                coefficient_one,
            )
    for remainder_seven in range(7):
        for units_ten in range(10):
            joined = crt_mod70_from_residues(remainder_seven, units_ten)
            assert 0 <= joined < 70
            assert joined % 7 == remainder_seven
            assert joined % 10 == units_ten


def test_mod70_word_monoid_preserves_concat_reflection_and_power_orientation() -> None:
    summary = DecimalMod70WordSummary.identity()
    for digit in map(int, "183"):
        summary = summary.then(DecimalMod70WordSummary.digit(digit))
    assert summary.packet() == _literal_mod70_packet("183")
    assert summary.reflected().packet() == _literal_mod70_packet("381")
    assert summary.power(3).packet() == _literal_mod70_packet("183183183")


@pytest.mark.parametrize("word", ("0", "5", "183", "49331684", "123456"))
def test_mod70_projection_has_spatial_copy_period_dividing_42(word: str) -> None:
    summary = DecimalMod70WordSummary.identity()
    for digit in map(int, word):
        summary = summary.then(DecimalMod70WordSummary.digit(digit))
    for copies in (1, 2, 6, 10**30 + 1):
        earlier = summary.power(copies)
        later = summary.power(copies + 42)
        assert earlier.packet() == later.packet()
        assert later.length - earlier.length == 42 * len(word)
