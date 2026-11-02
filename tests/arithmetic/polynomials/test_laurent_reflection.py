"""Moving-cut projections retain signed powers and exact coefficient order."""

import pytest

from number_compiler.arithmetic.polynomials.polynomial import (
    laurent_reflection_projections,
    polynomial_divide_exact,
)


@pytest.mark.parametrize("cut", [-3, 0, 2, 10**12])
def test_sparse_reflection_projects_without_cut_padding(cut: int) -> None:
    coefficients = (3, 0, -2, 4)
    symmetric, antisymmetric = laurent_reflection_projections(coefficients, cut)
    plus, minus = dict(symmetric), dict(antisymmetric)
    assert len(plus) <= 6
    assert len(minus) <= 6
    for index in plus.keys() | minus.keys():
        original = coefficients[index] if 0 <= index < len(coefficients) else 0
        assert plus.get(index, 0) + minus.get(index, 0) == 2 * original
        assert plus.get(index, 0) == plus.get(cut - index, 0)
        assert minus.get(index, 0) == -minus.get(cut - index, 0)


def test_zero_reflection_has_no_materialized_support() -> None:
    assert laurent_reflection_projections((0, 0), 10**12) == ((), ())


def test_exact_division_handles_zero_and_the_unit_without_looping() -> None:
    assert polynomial_divide_exact((0, 0), (-2, 1)) == (0,)
    assert polynomial_divide_exact((3, -2, 0), (1,)) == (3, -2)
    assert polynomial_divide_exact((0,), (1,)) == (0,)
    assert polynomial_divide_exact((1,), (-2, 1)) is None
