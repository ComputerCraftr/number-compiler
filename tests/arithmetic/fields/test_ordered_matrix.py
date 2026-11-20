"""Independent chronology and polynomial checks for supplied matrix words."""

import pytest

from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    OrderedCovector,
    OrderedMatrixProgram,
)


@pytest.mark.parametrize("modulus", [None, 2, 32, 1_000_000_007])
def test_noncommuting_repeat_prefix_and_covector(modulus: int | None) -> None:
    first, later = Matrix2.digit(2, modulus), Matrix2.digit(3, modulus)
    assert first.then(later) != later.then(first)
    program = OrderedMatrixProgram((first, later, Matrix2.upper_shear(-3, modulus)))
    for start in range(3):
        for length in (0, 1, 2, 3, 7, 16):
            p, q = 7, -2
            if modulus is not None:
                p, q = p % modulus, q % modulus
            for offset in range(length):
                a, b, c, d = program.letters[(start + offset) % 3].entries
                p, q = a * p + b * q, c * p + d * q
                if modulus is not None:
                    p, q = p % modulus, q % modulus
            action = program.product(start, length, repeat=True)
            assert action.apply(7, -2) == (p, q)
            covector = OrderedCovector((1, -2, 0, 3), modulus)
            assert covector.pullback(action).value(7, -2) == covector.value(p, q)


def test_ordered_repetition_is_not_separately_powered_factors() -> None:
    a, b = Matrix2.digit(3), Matrix2.digit(5)
    assert a.then(b).power(4) != a.power(4).then(b.power(4))
    covector = OrderedCovector((1, -2, 4))
    assert covector.pullback(a.then(b)) == covector.pullback(b).pullback(a)
    assert Matrix2.upper_shear(2).multiply(a) != a.multiply(Matrix2.upper_shear(2))


def test_large_modular_word_power_reads_one_cycle_and_remainder() -> None:
    program = OrderedMatrixProgram(tuple(Matrix2.digit(i, 97) for i in (1, 4, 2)))
    result = program.product_with_work(2, 3 * 10**30 + 2, repeat=True)
    assert result.letters_read == 5
    assert result.multiplications < 210
    assert result.matrix == program.product(2, 3, repeat=True).power(10**30).then(
        program.product(2, 2, repeat=True)
    )


def test_finite_word_refuses_unprovided_continuation_and_mixed_ring() -> None:
    program = OrderedMatrixProgram((Matrix2.digit(2), Matrix2.digit(3)))
    assert program.product(2, 0) == Matrix2.identity()
    with pytest.raises(ValueError):
        program.product(1, 2)
    with pytest.raises(ValueError):
        Matrix2.digit(2, 7).then(Matrix2.digit(3, 11))
    with pytest.raises(ValueError):
        OrderedCovector((1, 2), 7).pullback(Matrix2.digit(2, 11))
