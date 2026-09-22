"""Independent coefficient and convolution checks for centered F5 transport."""

from math import comb
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.polynomials.affine_transport import (
    radix_exponent_factors,
)
from number_compiler.arithmetic.polynomials.centered_f5 import CenteredF5Transport
from number_compiler.arithmetic.polynomials.f2_transport import F2SpatialTransport


def test_shared_frobenius_radix_walk_preserves_distinct_field_laws() -> None:
    for radix, exponent in ((2, (1 << 127) + (1 << 7) + 1), (5, 5**64 + 3)):
        factors = radix_exponent_factors(exponent, radix)
        assert (
            sum(stride * multiplicity for stride, multiplicity in factors) == exponent
        )
        assert all(0 < multiplicity < radix for _, multiplicity in factors)
        assert tuple(stride for stride, _ in factors) == tuple(
            sorted(stride for stride, _ in factors)
        )
    assert F2SpatialTransport(0, (1 << 127) + 1).frobenius_factors() == (
        (1, 1),
        (1 << 127, 1),
    )
    assert CenteredF5Transport(0, 5**64 + 3).frobenius_factors() == (
        (1, 3),
        (5**64, 1),
    )
    assert F2SpatialTransport(1, 5**64 + 3).frobenius_factors() == ()
    for bad in (True, -1, 1.0):
        with pytest.raises(ValueError):
            radix_exponent_factors(cast(int, bad), 5)


def test_centered_coefficients_and_frobenius_expansion() -> None:
    for q in range(5):
        for r in range(51):
            operator = CenteredF5Transport(q, r)
            expected = {
                2 * k - r: pow(2, q, 5) * comb(r, k) % 5
                for k in range(r + 1)
                if comb(r, k) % 5
            }
            assert dict(operator.shifts()) == expected
            for offset in range(-r - 1, r + 2):
                assert operator.coefficient(offset) == expected.get(offset, 0)


def test_composition_is_convolution_and_canonicalizes_no_growth_period() -> None:
    assert CenteredF5Transport(8, 13) == CenteredF5Transport(0, 13)
    for r in range(13):
        first = CenteredF5Transport(3, r)
        second = CenteredF5Transport(2, 12 - r)
        convolution: dict[int, int] = {}
        for x, a in first.shifts():
            for y, b in second.shifts():
                convolution[x + y] = (convolution.get(x + y, 0) + a * b) % 5
        assert dict(first.then(second).shifts()) == {
            x: a for x, a in convolution.items() if a
        }
        assert first.then(second) == second.then(first)


def test_large_sparse_transport_stays_sparse_and_dense_transport_fails_closed() -> None:
    degree = 5**40
    operator = CenteredF5Transport(0, degree)
    assert operator.shifts(max_terms=2) == ((-degree, 1), (degree, 1))
    assert operator.coefficient(0) == 0
    with pytest.raises(BlockContextBudgetExceeded):
        CenteredF5Transport(0, degree - 1).shifts(max_terms=4096)
    for bad in (True, -1, 1.0):
        with pytest.raises(ValueError):
            CenteredF5Transport(cast(int, bad), 0)
        with pytest.raises(ValueError):
            operator.shifts(max_terms=cast(int, bad))
