"""Independent finite checks for the F5/parity decimal carry cocycle."""

from itertools import product

import pytest

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_add_cocycle,
    decimal_cocycle_coordinates,
    decimal_cocycle_domain,
    decimal_cocycle_kappa,
    decimal_cocycle_value,
    decimal_crt_digit,
    decimal_factored_coordinates,
    decimal_normalize_cocycle,
)


@pytest.mark.algebra
def test_crt_digit_is_the_exact_f5_parity_bijection() -> None:
    observed: set[int] = set()
    for alpha, epsilon in product(range(5), range(2)):
        digit = decimal_crt_digit(alpha, epsilon)
        assert digit % 5 == alpha
        assert digit % 2 == epsilon
        observed.add(digit)
    assert observed == set(range(10))


@pytest.mark.algebra
def test_cocycle_carrier_round_trips_all_pair_symbols() -> None:
    for symbol in range(19):
        domain, alpha, epsilon = decimal_cocycle_coordinates(symbol)
        assert alpha == symbol % 5
        assert epsilon == symbol % 2
        assert decimal_cocycle_value(domain, alpha, epsilon) == symbol
        old_domain, old_alpha, beta = decimal_factored_coordinates(symbol)
        assert domain is old_domain
        assert alpha == old_alpha
        assert epsilon == (alpha + beta) % 2


@pytest.mark.algebra
def test_cocycle_normalization_is_affine_in_both_channels() -> None:
    for alpha, epsilon, carry in product(range(5), range(2), range(2)):
        digit = decimal_crt_digit(alpha, epsilon)
        normalized = decimal_normalize_cocycle(alpha, epsilon, carry)
        assert normalized == ((alpha + carry) % 5, epsilon ^ carry)
        assert decimal_crt_digit(*normalized) == (digit + carry) % 10


@pytest.mark.algebra
def test_cocycle_adder_exhausts_decimal_digits_and_isolates_kappa() -> None:
    coordinates = tuple(product(range(5), range(2)))
    for left, right in product(coordinates, repeat=2):
        x = decimal_crt_digit(*left)
        y = decimal_crt_digit(*right)
        expected = x + y
        domain, alpha, epsilon, kappa = decimal_add_cocycle(left, right)
        assert alpha == (left[0] + right[0]) % 5
        assert epsilon == left[1] ^ right[1]
        assert kappa == decimal_cocycle_kappa(left, right) == int(expected >= 10)
        assert domain is decimal_cocycle_domain(alpha, epsilon, kappa)
        assert domain is (
            CarryFn.CONST1
            if expected > 9
            else CarryFn.ID
            if expected == 9
            else CarryFn.CONST0
        )
        assert decimal_cocycle_value(domain, alpha, epsilon) == expected


@pytest.mark.algebra
def test_eq_and_out_of_alphabet_cocycle_coordinates_are_exact() -> None:
    assert decimal_add_cocycle((4, 0), (0, 1)) == (CarryFn.ID, 4, 1, 0)
    with pytest.raises(ValueError, match="outside the decimal pair image"):
        decimal_cocycle_domain(4, 1, 1)
    with pytest.raises(ValueError, match="value 9 requires EQ"):
        decimal_cocycle_value(CarryFn.CONST0, 4, 1)
    with pytest.raises(ValueError, match="value 9 requires EQ"):
        decimal_cocycle_value(CarryFn.CONST1, 4, 1)


@pytest.mark.algebra
def test_growth_interior_uses_the_reflected_carry_index() -> None:
    # Source (16,16) has carries c=(0,1,1), normalized digits (6,7), and
    # growth digits (6,7,1).  The interior pairs digit 7 with its reflection,
    # not with the spatially preceding normalized digit 6.
    alpha, epsilon = decimal_cocycle_coordinates(16)[1:]
    first = decimal_normalize_cocycle(alpha, epsilon, 0)
    second = decimal_normalize_cocycle(alpha, epsilon, 1)
    actual = decimal_add_cocycle(second, second)
    adjacent_shorthand = decimal_add_cocycle(second, first)
    assert decimal_cocycle_value(actual[0], actual[1], actual[2]) == 14
    assert (
        decimal_cocycle_value(
            adjacent_shorthand[0], adjacent_shorthand[1], adjacent_shorthand[2]
        )
        == 13
    )
