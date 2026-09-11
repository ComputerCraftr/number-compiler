"""Finite proof checks for the exact decimal successor channel laws."""

from itertools import product

import pytest

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_add_factored,
    decimal_factored_coordinates,
    decimal_factored_value,
    decimal_normalize_factored,
)


@pytest.mark.algebra
def test_factored_normalizer_exhausts_f5_f2_and_carry() -> None:
    for alpha, beta, carry in product(range(5), range(2), range(2)):
        normalized = decimal_normalize_factored(alpha, beta, carry)
        wrap = int(alpha == 4 and carry == 1)
        assert normalized == ((alpha + carry) % 5, beta ^ wrap)
        assert normalized[0] + 5 * normalized[1] == (alpha + 5 * beta + carry) % 10


@pytest.mark.algebra
def test_factored_pair_adder_exhausts_both_normalized_digits() -> None:
    coordinates = tuple(product(range(5), range(2)))
    for left, right in product(coordinates, repeat=2):
        domain, alpha, beta = decimal_add_factored(left, right)
        threshold = int(left[0] + right[0] >= 5)
        majority = int(left[1] + right[1] + threshold >= 2)
        expected = left[0] + 5 * left[1] + right[0] + 5 * right[1]
        assert alpha == (left[0] + right[0]) % 5
        assert beta == left[1] ^ right[1] ^ threshold
        assert domain is (
            CarryFn.CONST1
            if majority
            else CarryFn.ID
            if expected == 9
            else CarryFn.CONST0
        )
        assert decimal_factored_value(domain, alpha, beta) == expected


@pytest.mark.algebra
def test_factored_domain_is_exactly_lt_eq_or_gt() -> None:
    expected_domains = (
        *(CarryFn.CONST0 for _ in range(9)),
        CarryFn.ID,
        *(CarryFn.CONST1 for _ in range(9)),
    )
    for symbol, expected_domain in enumerate(expected_domains):
        domain, alpha, beta = decimal_factored_coordinates(symbol)
        assert domain is expected_domain
        assert decimal_factored_value(domain, alpha, beta) == symbol

    assert decimal_factored_coordinates(2) == (CarryFn.CONST0, 2, 0)
    assert decimal_factored_coordinates(4) == (CarryFn.CONST0, 4, 0)
    assert decimal_factored_coordinates(8) == (CarryFn.CONST0, 3, 1)
    assert decimal_factored_coordinates(16) == (CarryFn.CONST1, 1, 1)


@pytest.mark.algebra
def test_factored_domain_rejects_noncanonical_coordinates() -> None:
    # Nine is the unique EQ value, while 19 is outside the pair alphabet.
    with pytest.raises(ValueError, match="value 9 requires EQ"):
        decimal_factored_value(CarryFn.CONST0, 4, 1)
    with pytest.raises(ValueError, match="value 9 requires EQ"):
        decimal_factored_value(CarryFn.CONST1, 4, 1)
    for alpha, beta in product(range(5), range(2)):
        if (alpha, beta) == (4, 1):
            assert decimal_factored_value(CarryFn.ID, alpha, beta) == 9
        else:
            with pytest.raises(ValueError, match="EQ requires"):
                decimal_factored_value(CarryFn.ID, alpha, beta)


@pytest.mark.algebra
def test_factored_laws_reject_numeric_aliases() -> None:
    for value in (True, 0.0, -1, 5):
        with pytest.raises((TypeError, ValueError)):
            decimal_normalize_factored(value, 0, 0)  # type: ignore[arg-type]
    for value in (True, 0, 1, 2):
        with pytest.raises(TypeError):
            decimal_factored_value(value, 0, 0)  # type: ignore[arg-type]
