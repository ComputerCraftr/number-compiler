from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.ordered_output import (
    OrderedBandChannel,
    OrderedBandOutput,
    OrderedPhaseCoordinate,
)
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.semantic_oracles import literal_band_trace


def _literal_states(seed: int, generation: int, steps: int) -> tuple[int, ...]:
    current = seed
    for _ in range(generation):
        current += int(str(current)[::-1])
    states: list[int] = []
    for _ in range(steps):
        states.append(current)
        current += int(str(current)[::-1])
    return tuple(states)


def test_ordered_digit_band_uses_exact_issued_reverse_add_children() -> None:
    term = ReverseAddPoweredTerm(196, 2, base=10)
    states = _literal_states(196, 2, 3)
    packet = term.ordered_digit_band(3, 3, 101, trace=True)

    expected_lower, expected_upper, expected_trace, expected_reads = literal_band_trace(
        states, 3, 101
    )

    assert type(packet) is OrderedBandOutput
    assert packet.channels == (
        OrderedBandChannel.LOWER_DIGITS,
        OrderedBandChannel.UPPER_DIGITS,
    )
    assert packet.matrices == (expected_lower, expected_upper)
    assert packet.trace == tuple(expected_trace)
    assert packet.source_index == 2
    assert packet.physical_ticks == 3
    assert packet.start_phase is None
    assert packet.terminal_phase is None
    assert packet.phase_coordinate is OrderedPhaseCoordinate.NONE
    assert packet.source_coverage == "exact-issued-q19-child-path"
    assert packet.source_letters_read == expected_reads
    assert packet.matrix_multiplications == 2 * 3 * (3 + 1)


def test_ordered_digit_band_reports_empty_trace_when_not_demanded() -> None:
    packet = ReverseAddPoweredTerm(196, 2).ordered_digit_band(1, 2, 97)
    assert packet.trace == ()
    assert packet.physical_ticks == 1


def test_one_tick_band_does_not_publish_an_unrequested_successor() -> None:
    term = ReverseAddPoweredTerm(196, 2)
    term.completed_q19_occurrence()
    before = term.resource_ledger.counters.get(
        _reverse_add_keys.REVERSE_Q19_PRIMITIVE_PAIR_APPLICATIONS, 0
    )
    term.ordered_digit_band(1, 2, 97)
    after = term.resource_ledger.counters.get(
        _reverse_add_keys.REVERSE_Q19_PRIMITIVE_PAIR_APPLICATIONS, 0
    )
    assert after == before


def test_ordered_reverse_add_band_explains_generation_zero_admission() -> None:
    with pytest.raises(ValueError, match="completed positive-generation Q19"):
        ReverseAddPoweredTerm(196, 0).ordered_digit_band(1, 2, 97)
