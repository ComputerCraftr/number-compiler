from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.ordered_output import (
    OrderedBandChannel,
    OrderedBandOutput,
    OrderedPhaseCoordinate,
)
from number_compiler.arithmetic.fields.ordered_matrix import OrderedCovector
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from tests.support.semantic_oracles import literal_band_trace, literal_digit_matrix


def _literal_states(seed: int, generation: int, steps: int) -> tuple[int, ...]:
    current = seed
    for _ in range(generation):
        current = 2 * int(str(current)[::-1])
    states: list[int] = []
    for _ in range(steps):
        states.append(current)
        current = 2 * int(str(current)[::-1])
    return tuple(states)


def test_ordered_digit_band_matches_literal_seed196_ticks_and_covectors() -> None:
    term = DoubleReverseTerm(196, 2, max_steps=4)
    states = _literal_states(196, 2, 2)
    packet = term.ordered_digit_band(2, 3, 97, coefficients=(1, -2, 0, 1), trace=True)

    expected_lower, expected_upper, expected_trace, expected_reads = literal_band_trace(
        states, 3, 97
    )

    assert type(packet) is OrderedBandOutput
    assert packet.channels == (
        OrderedBandChannel.LOWER_DIGITS,
        OrderedBandChannel.UPPER_DIGITS,
    )
    assert packet.matrices == (expected_lower, expected_upper)
    assert packet.trace == tuple(expected_trace)
    assert packet.covectors == tuple(
        OrderedCovector((1, -2, 0, 1), 97).pullback(matrix)
        for matrix in packet.matrices
    )
    assert packet.source_index == 2
    assert packet.physical_ticks == 2
    assert packet.start_phase is None
    assert packet.terminal_phase is None
    assert packet.phase_coordinate is OrderedPhaseCoordinate.NONE
    assert packet.source_coverage == "exact-scheduler-issued-physical-window"
    assert packet.source_letters_read == expected_reads
    assert packet.matrix_multiplications == 2 * 2 * (3 + 1)


def test_ordered_digit_band_pads_short_source_windows_and_preserves_zero() -> None:
    term = DoubleReverseTerm(0, 1, max_steps=3)
    packet = term.ordered_digit_band(2, 3, 101, trace=True)
    identity_digit = literal_digit_matrix("000", 101)
    two_tick_identity = identity_digit.then(identity_digit)
    assert packet.matrices == (two_tick_identity, two_tick_identity)
    assert packet.trace == ((identity_digit, identity_digit),) * 2
    assert packet.source_letters_read == 4


def test_ordered_digit_band_refuses_a_reset_of_absolute_step_budget() -> None:
    term = DoubleReverseTerm(196, 2, max_steps=2)
    with pytest.raises(BlockContextBudgetExceeded, match="remaining source step"):
        term.ordered_digit_band(1, 2, 97)


def test_ordered_digit_band_checks_trace_limit_before_source_construction() -> None:
    term = DoubleReverseTerm(1, 0, max_steps=129)
    with pytest.raises(ValueError, match="128 physical ticks"):
        term.ordered_digit_band(129, 1, 97, trace=True)
