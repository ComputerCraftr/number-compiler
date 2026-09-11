from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.polynomials.cyclotomic_factor import (
    cyclotomic_factors_mod_prime,
    cyclotomic_primary_components,
)
from number_compiler.arithmetic.polynomials.cyclotomic_lift import (
    cyclotomic_binary_lift_marker,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock

if TYPE_CHECKING:
    from number_compiler.arithmetic.polynomials.cyclotomic_lift import (
        CyclotomicLiftMarker,
    )


def test_phi2_signed_hensel_marker_is_scalar_and_distinguishes_minus_one_lift() -> None:
    width = 8
    power = 7
    plus = (1,) + (0,) * (width - 1)
    minus = (-1,) + (0,) * (width - 1)

    def marker(
        digits: tuple[int, ...],
    ) -> CyclotomicLiftMarker:
        lo = CyclotomicDigitBlock.from_coefficients(
            digits,
            order=2,
            modulus=2,
            power=power,
            length=width,
        )
        hi = CyclotomicDigitBlock.from_coefficients(
            digits,
            order=2,
            modulus=4,
            power=power,
            length=width,
        )
        return cyclotomic_binary_lift_marker(lo, hi)

    mp = marker(plus)
    mm = marker(minus)
    assert mp.canonical_key != mm.canonical_key
    assert not hasattr(mp, "layer") and not hasattr(mp, "residue")
    assert {mp.first_orientation, mm.first_orientation} == {0, 1}


def test_mersenne_sign_invariant_lift_marker_preserves_global_pm_quotient() -> None:
    p = 7
    modulus = (1 << p) - 1
    factor2 = cyclotomic_factors_mod_prime(p, 2)[0]

    def lifted_factor(precision: int) -> tuple[int, ...]:
        for factor in cyclotomic_primary_components(p, 2, precision):
            if tuple(v & 1 for v in factor) == factor2:
                return factor
        raise AssertionError

    f2 = lifted_factor(1)
    f4 = lifted_factor(2)

    def marker(value: int) -> tuple[object, ...]:
        digits = digits_lsd(value % modulus, 2, p)
        lo = CyclotomicDigitBlock.from_coefficients(
            digits,
            order=p,
            modulus=2,
            factor=f2,
            length=p,
        )
        hi = CyclotomicDigitBlock.from_coefficients(
            digits,
            order=p,
            modulus=4,
            factor=f4,
            length=p,
        )
        return cyclotomic_binary_lift_marker(lo, hi, sign_invariant=True).canonical_key

    for value in (1, 2, 3, 5, 17, 31, 63):
        assert marker(value) == marker((-value) % modulus)
