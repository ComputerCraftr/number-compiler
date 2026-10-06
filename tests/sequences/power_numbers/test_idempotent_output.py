"""Special-number output observers at nontrivial CRT idempotents."""

from number_compiler.arithmetic.fields.idempotent_output import IdempotentModElement
from number_compiler.sequences.power_numbers.idempotent_output import (
    IdempotentSpecialDigitBlock,
)


def test_digit_length_and_carry_are_evaluated_after_nontrivial_idempotent_specialization() -> (
    None
):
    # M11 = 23*89.  This idempotent is 1 mod 23 and 0 mod 89.
    modulus = 2047
    e = 1335
    assert e * e % modulus == e
    block = IdempotentSpecialDigitBlock(
        "mersenne",
        11,
        IdempotentModElement.generator(modulus),
    )

    # For the formal generator E, Boolean endpoints are 0 and 1.  They agree
    # on bit 10, canonical length, and LL end-around carry.  The nontrivial CRT
    # specialization disagrees on all three, so endpoint equality alone is not
    # a valid nonlinear-observer quotient.
    assert block.endpoint_digit_pair(10) == (0, 0)
    assert block.digit_at_idempotent(10, e) == 1
    assert block.endpoint_length_pair() == (1, 1)
    assert block.length_at_idempotent(e) == 11
    assert block.endpoint_square_boundary_carries() == (-1, -1)
    assert block.square_boundary_carry_at_idempotent(e) == 4
