"""The root coordinate obeys exact rational algebra, not source equivalence."""

from fractions import Fraction
from itertools import product

import pytest

from number_compiler.arithmetic.fields.consumer_pullback import ExactRational
from number_compiler.arithmetic.fields.root_semifield import RootSemifieldElement


def rational(value: RootSemifieldElement) -> Fraction:
    return Fraction(value.square.numerator, value.square.denominator)


def test_root_operations_match_independent_rational_arithmetic() -> None:
    values = [Fraction(0), Fraction(1, 3), Fraction(1), Fraction(7, 2)]
    for a, b in product(values, repeat=2):
        left = RootSemifieldElement(ExactRational(a.numerator, a.denominator))
        right = RootSemifieldElement(ExactRational(b.numerator, b.denominator))
        assert rational(left.root_sum(right)) == a + b
        assert rational(left.multiply(right)) == a * b
        assert rational(left.tropical_min(right)) == min(a, b)
        if a >= b:
            assert rational(left.root_difference(right)) == a - b
        else:
            with pytest.raises(ValueError):
                left.root_difference(right)
        if b:
            assert rational(left.divide(right)) == a / b
        for exponent in (0, 1, 2, 9):
            assert rational(left.power(exponent)) == a**exponent


def test_root_admission_and_partial_operations() -> None:
    with pytest.raises(TypeError):
        RootSemifieldElement(True)
    with pytest.raises(ValueError):
        RootSemifieldElement(-1)
    with pytest.raises(ZeroDivisionError):
        RootSemifieldElement.zero().reciprocal()
    with pytest.raises(ValueError):
        RootSemifieldElement.one().power(True)
