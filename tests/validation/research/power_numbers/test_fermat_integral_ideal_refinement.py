"""Refinement checks connecting the integer cochain to ideal membership."""

from __future__ import annotations

from devtools.verification.fermat_integral_ideal_reference import (
    FermatIntegralIdealWitness,
)


def test_integral_carry_identity_evaluates_to_the_pepin_ideal() -> None:
    witness = FermatIntegralIdealWitness.from_source(2)
    width = witness.width
    candidate = (1 << width) + 1
    source_value = 3**witness.exponent
    folded_value = sum(
        coefficient * (1 << position)
        for position, coefficient in enumerate(witness.folded)
    )
    emitted_value = sum(
        digit * (1 << position) for position, digit in enumerate(witness.signed_digits)
    )

    # Exact binomial folding gives P(2) = A(2) modulo 2**w+1.
    quotient, remainder = divmod(source_value - folded_value, candidate)
    assert remainder == 0
    # Summing a_i+c_i=e_i+2*c_(i+1) with weights 2**i and c_w=-c_0
    # gives A(2)-E(2)=-c_0*(2**w+1), over the integers.
    assert folded_value - emitted_value == -witness.carries[0] * candidate
    assert source_value - emitted_value == (quotient - witness.carries[0]) * candidate
    assert emitted_value == -1
    assert witness.terminal_result() == "PRIME"


def test_f4_bounded_integral_source_certificate_is_positive() -> None:
    # Keep the 32,769-term source construction in the research validation lane.
    witness = FermatIntegralIdealWitness.from_source(4)
    assert witness.terminal
    assert witness.exponent + 1 == 32_769
    assert witness.signed_digits == (-1,) + (0,) * (witness.width - 1)
    assert witness.terminal_result() == "PRIME"
