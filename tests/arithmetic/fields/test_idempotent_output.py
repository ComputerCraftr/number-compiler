"""CRT idempotent arithmetic and specialized digit-block semantics."""

import pytest

from number_compiler.arithmetic.fields.idempotent_output import (
    IdempotentCyclotomicDigitBlock,
    IdempotentModElement,
)
from number_compiler.arithmetic.fields.morphism_core import QuadraticPower
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock


def test_idempotent_rank_two_arithmetic_specializes_exactly_on_all_crt_sheets() -> None:
    modulus = 15
    x = IdempotentModElement(modulus, 4, 7)
    y = IdempotentModElement(modulus, 8, 11)
    for e in (0, 1, 6, 10):
        xv = x.specialize_idempotent(e)
        yv = y.specialize_idempotent(e)
        assert x.add(y).specialize_idempotent(e) == (xv + yv) % modulus
        assert x.subtract(y).specialize_idempotent(e) == (xv - yv) % modulus
        assert x.multiply(y).specialize_idempotent(e) == xv * yv % modulus
        assert x.square().specialize_idempotent(e) == xv * xv % modulus
    with pytest.raises(ValueError, match="not-idempotent"):
        x.specialize_idempotent(2)


def test_sheet_conversion_and_shared_quadratic_power_need_no_parallel_power_kernel() -> (
    None
):
    modulus = 65537
    value = IdempotentModElement.from_sheets(modulus, 3, 5)
    assert value.sheets == (3, 5)
    powered = QuadraticPower(4).apply_iterated(value, step=lambda item: item.square())
    assert powered.sheets == (
        pow(3, 1 << 4, modulus),
        pow(5, 1 << 4, modulus),
    )


def test_unified_cyclotomic_digit_block_lifts_componentwise_and_specializes() -> None:
    zero = CyclotomicDigitBlock.from_coefficients((2, 3), order=2, modulus=15)
    one = CyclotomicDigitBlock.from_coefficients((7, 4), order=2, modulus=15)
    lifted = IdempotentCyclotomicDigitBlock(zero, one)
    squared = lifted.square().add_constant(3)
    assert squared.zero_sheet.residue == zero.square().add_constant(3).residue
    assert squared.one_sheet.residue == one.square().add_constant(3).residue

    # e=6 is a genuine nontrivial idempotent modulo 15.  Specialization is
    # coefficientwise interpolation in the existing cyclotomic ring.
    specialized = lifted.specialize_idempotent(6)
    expected = zero.add(one.subtract(zero).scale_coefficients(6))
    assert specialized.residue == expected.residue
