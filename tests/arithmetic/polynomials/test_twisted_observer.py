from math import gcd

import pytest

from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
    first_mirror_obstruction,
)
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)
from number_compiler.arithmetic.fields.tropical_divisor import TropicalDivisorState


def test_twisted_evaluation_commutes_only_at_compatible_moduli() -> None:
    coefficients = (7, -3, 0, 4, 9, -1, 3, 2, 5)
    for width in range(2, 8):
        for sign in (-1, 1):
            modulus = 2**width - sign
            projection = TwistedCylinderProjection.observe(
                iter(coefficients), width=width, sign=sign
            )
            assert projection.support(radix=2, modulus=modulus).divisor == gcd(
                modulus, sum(c * 2**i for i, c in enumerate(coefficients))
            )
    with pytest.raises(ValueError, match="incompatible"):
        projection.support(radix=2, modulus=11)


def test_fermat_and_mersenne_tiles_emit_support_from_the_same_square() -> None:
    for family, width in (("fermat", 4), ("mersenne", 11)):
        spec = ArithmeticTileSpec(family, width)
        for value in (0, 1, 5, 17, 23):
            step, projection = ArithmeticTile.from_value(
                spec, value
            ).step_with_twisted_projection(width=width, sign=spec.boundary_sign)
            assert projection.support(radix=2, modulus=spec.modulus).divisor == gcd(
                spec.modulus, value * value + spec.addend
            )
            assert step.convolution.scalar_multiplications >= 0


def test_mirror_ladder_is_an_exact_current_target_certificate() -> None:
    for n in range(1, 400):
        digits = tuple(map(int, str(n)))
        projection = first_mirror_obstruction(len(digits), digits.__getitem__)
        assert (projection is None) == (digits == digits[::-1])
        if projection:
            assert projection.nonzero
    # A vanishing first sheet is insufficient: refine past cancellation.
    assert first_mirror_obstruction(4, (1, 2, 4, 1).__getitem__) is not None


def test_tropical_divisor_operations_and_cancellation_boundary() -> None:
    for n in (15, 16, 45, 72):
        for a in range(n):
            for b in range(n):
                left, right = (
                    TropicalDivisorState.observe(n, a),
                    TropicalDivisorState.observe(n, b),
                )
                assert left.multiply(right) == TropicalDivisorState.observe(n, a * b)
                assert left.meet(right).divisor == gcd(n, gcd(a, b))
                assert n % left.join(right).divisor == 0
    # Same separate valuations, different sum support: addition is not meet.
    assert TropicalDivisorState.observe(15, 1) == TropicalDivisorState.observe(15, 4)
    assert TropicalDivisorState.observe(15, 1 + 4).proper_factor == 5
    assert TropicalDivisorState.observe(15, 1 + 1).proper_factor is None


def test_nontrivial_crt_root_factor_comes_from_the_same_family_field() -> None:
    for family, width, factor, cofactor in (
        ("mersenne", 11, 23, 89),
        ("fermat", 32, 641, 6700417),
    ):
        spec = ArithmeticTileSpec(family, width)
        defect = factor * ((-2 * pow(factor, -1, cofactor)) % cofactor)
        assert defect * (defect + 2) % spec.modulus == 0
        _, projection = ArithmeticTile.from_value(
            spec, defect
        ).step_with_twisted_projection(width=width, sign=spec.boundary_sign)
        assert (
            projection.support(
                radix=2, modulus=spec.modulus, constant=-spec.addend
            ).proper_factor
            == factor
        )
