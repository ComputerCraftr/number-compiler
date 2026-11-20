"""Bounded exact tests for shared dyadic unit and carry/borrow projections."""

from __future__ import annotations

from typing import Literal

import pytest

from number_compiler.arithmetic.fields.dyadic_unit_phase import (
    DyadicUnitPhase,
    dyadic_borrow_frontier,
    dyadic_carry_frontier,
)

_UNIT_BASES: tuple[Literal[3, 5, 15], ...] = (3, 5, 15)


@pytest.mark.parametrize("base", _UNIT_BASES)
@pytest.mark.parametrize("precision", (1, 2, 3, 4, 9, 32))
def test_unit_phase_uses_exact_dyadic_period(
    base: Literal[3, 5, 15], precision: int
) -> None:
    phase = DyadicUnitPhase.from_exponent(base, 137, precision)
    modulus = 1 << precision
    if base == 15 and 2 <= precision <= 5:
        assert phase.order == 2
    assert phase.multiplier == pow(base, 137, modulus)
    assert phase.advance(23).multiplier == pow(base, 160, modulus)
    assert phase.square().multiplier == pow(base, 274, modulus)
    assert phase.power(5).multiplier == pow(base, 685, modulus)


def test_carry_frontier_matches_low_column_affine_carries_and_preserves_order() -> None:
    phase = DyadicUnitPhase.from_exponent(3, 37, 48)
    reserve_calls: list[int] = []

    def reserve(bits: int) -> None:
        reserve_calls.append(bits)

    positions = (11, 1, 7, 11, 0)
    result = dyadic_carry_frontier(
        phase,
        source=0xA53,
        offset=0x13,
        positions=positions,
        carry_width=8,
        reserve_bits=reserve,
    )
    multiplier = pow(3, 37, 1 << 48)
    expected = tuple(
        ((multiplier * (0xA53 % (1 << cut)) + (0x13 % (1 << cut))) >> cut) & 0xFF
        for cut in positions
    )
    assert tuple(cut.position for cut in result.cuts) == positions
    assert tuple(cut.carry for cut in result.cuts) == expected
    assert reserve_calls == [
        8
        * (
            max(positions)
            + 8
            + 0xA53.bit_length()
            + 0x13.bit_length()
            + len(positions) * (8 + 64)
            + 64
        )
    ]


@pytest.mark.parametrize("position", (0, 1, 6, 17))
def test_borrow_frontier_reports_incoming_outgoing_borrows_and_exact_chunks(
    position: int,
) -> None:
    raw_phase = DyadicUnitPhase.from_exponent(15, 13, position + 5)
    correction_phase = DyadicUnitPhase.from_exponent(5, 13, position + 5)
    raw_source = 0x1B7
    correction_source = 0x235
    result = dyadic_borrow_frontier(
        raw_phase,
        raw_source,
        correction_phase,
        correction_source,
        (position,),
        chunk_width=5,
        reserve_bits=lambda _bits: None,
    )
    raw = 15**13 * raw_source
    correction = 5**13 * correction_source
    incoming = int(raw % (1 << position) < correction % (1 << position))
    outgoing_position = position + 5
    outgoing = int(
        raw % (1 << outgoing_position) < correction % (1 << outgoing_position)
    )
    raw_chunk = (raw >> position) & 31
    correction_chunk = (correction >> position) & 31
    physical_chunk = (raw_chunk - correction_chunk - incoming) & 31
    cut = result.cuts[0]
    assert (cut.borrow_in, cut.borrow_out) == (incoming, outgoing)
    assert (cut.raw_chunk, cut.correction_chunk, cut.physical_chunk) == (
        raw_chunk,
        correction_chunk,
        physical_chunk,
    )


def test_frontiers_reject_untrusted_precision_and_noncanonical_phases() -> None:
    with pytest.raises(ValueError):
        DyadicUnitPhase(3, 4, 4)
    phase = DyadicUnitPhase.from_exponent(5, 3, 8)
    with pytest.raises(ValueError):
        dyadic_carry_frontier(
            phase,
            9,
            1,
            (8,),
            carry_width=1,
            reserve_bits=lambda _bits: None,
        )
    with pytest.raises(TypeError):
        DyadicUnitPhase.from_exponent(3, True, 8)
