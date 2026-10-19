"""Independent finite-polynomial checks for shared harmonic observations."""

from itertools import product

from number_compiler.arithmetic.polynomials.polynomial import f5_modes


def test_f5_modes_match_independent_powers_in_coefficient_order() -> None:
    for width in range(5):
        for coefficients in product((-1, 0, 2), repeat=width):
            expected = tuple(
                sum(value * z**index for index, value in enumerate(coefficients)) % 5
                for z in (1, 2, 3, 4)
            )
            assert f5_modes(coefficients) == expected


def test_unknown_harmonic_coefficients_are_not_zeroes() -> None:
    for index in range(4):
        coefficients: list[int | None] = [1, 2, 3, 4]
        coefficients[index] = None
        assert f5_modes(coefficients) is None
    assert f5_modes(()) == (0, 0, 0, 0)
    assert f5_modes((0, 0)) == (0, 0, 0, 0)


def test_f5_modes_do_not_materialize_positional_powers() -> None:
    # Four equal coefficients cancel at the three nonidentity F5 characters.
    # A long exact input checks bounded accumulation, independent of pow().
    assert f5_modes((1,) * 10000) == (0, 0, 0, 0)
