from __future__ import annotations

from number_compiler.arithmetic.polynomials.cyclotomic import cyclotomic_coefficients
from number_compiler.arithmetic.polynomials.cyclotomic_factor import (
    cyclotomic_factors_mod_prime_power,
    cyclotomic_linear_factor_profile,
    cyclotomic_primary_components,
    polynomial_crt_mod_prime_power,
)
from number_compiler.arithmetic.polynomials.polynomial import (
    polynomial_multiply,
    polynomial_remainder_monic,
)


def _product(
    polys: tuple[tuple[int, ...], ...] | tuple[tuple[int, ...], tuple[int, ...]],
) -> tuple[int, ...]:
    out: tuple[int, ...] = (1,)
    for poly in polys:
        out = polynomial_multiply(out, poly)
    return out


def test_hensel_lift_phi7_binary_factors_to_mod8_exactly() -> None:
    factors = cyclotomic_factors_mod_prime_power(7, 2, 3)
    assert len(factors) == 2
    assert all(len(factor) == 4 and factor[-1] == 1 for factor in factors)
    q = 8
    product = _product(factors)
    source = cyclotomic_coefficients(7)
    length = max(len(product), len(source))
    assert tuple([c % q for c in product] + [0] * (length - len(product))) == tuple(
        [c % q for c in source] + [0] * (length - len(source))
    )


def test_prime_power_crt_round_trip_on_hensel_components() -> None:
    p, k, q = 2, 3, 8
    factors = cyclotomic_factors_mod_prime_power(7, p, k)
    source = (3, 5, 7, 1, 6, 2)
    residues = tuple(
        polynomial_remainder_monic(source, factor, modulus=q) for factor in factors
    )
    reconstructed = polynomial_crt_mod_prime_power(residues, factors, p, k)
    whole = _product(factors)
    assert reconstructed == polynomial_remainder_monic(source, whole, modulus=q)


def test_ramified_power_two_cyclotomic_channel_stays_one_primary_component() -> None:
    # Phi_8=z^4+1 has the repeated root (z+1)^4 mod 2.  It must not be
    # presented as four independent CRT factors over Z/32.
    components = cyclotomic_primary_components(8, 2, 5)
    assert len(components) == 1
    assert components[0] == tuple(c % 32 for c in cyclotomic_coefficients(8))


def test_linear_normalization_kernel_profile_is_constant_size_theorem() -> None:
    # In the ternary/2-adic Phi_8 channel, 3-z is singular because Phi_8(3)=82.
    profile = cyclotomic_linear_factor_profile(8, 3, 32)
    assert profile.evaluation == 82
    assert profile.kernel_size == profile.cokernel_size == 2
    assert profile.image_size * profile.kernel_size == 32**profile.degree
    assert not profile.unit
    # Decimal normalization in the same 2-adic channel is a unit.
    assert cyclotomic_linear_factor_profile(8, 10, 32).unit


def test_digit_block_prime_power_components_round_trip_and_ramification_guard() -> None:
    from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
        CyclotomicDigitBlock,
    )

    whole = CyclotomicDigitBlock.from_coefficients(
        (1, 2, 3, 4, 5, 6),
        order=7,
        modulus=8,
        length=6,
    )
    parts = whole.prime_power_components(prime=2, precision=3)
    assert len(parts) == 2 and all(part.factor is not None for part in parts)
    rebuilt = CyclotomicDigitBlock.from_prime_power_components(
        parts, prime=2, precision=3
    )
    assert rebuilt.equivalent(whole) and rebuilt.length == whole.length

    ramified = CyclotomicDigitBlock.from_coefficients(
        (1, 0, 1),
        order=8,
        modulus=32,
        length=3,
    )
    assert ramified.prime_power_components(prime=2, precision=5) == (ramified,)
