"""Guarded observation words agree with an independent normalized orbit."""

from typing import cast

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import MixedParityMotif
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
    admit_boundary_macro_plan,
    select_boundary_macro,
)
from number_compiler.sequences.collatz.innovation_port_moore import SIGNED_SYMBOLS
from number_compiler.sequences.collatz.innovation_temporal_tape import (
    observed_innovation_macro_tape,
)
from number_compiler.sequences.collatz.mixed_clock_macros import (
    select_mixed_clock_macro,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def _literal_word(source: int, steps: int, modulus: int) -> tuple[str, ...]:
    symbols = []
    for _ in range(steps):
        branch = source % 4
        if branch == 0:
            left, right, label = source // 2, source // 4, "B"
        elif branch == 1:
            left, right, label = (source + 1) // 2, (3 * source + 1) // 4, "N"
        elif branch == 2:
            left, right, label = source // 2, (source + 2) // 4, "A"
        else:
            left, right, label = (3 * source + 3) // 4, (source + 1) // 2, "B"
        flag = (
            left % modulus < right % modulus
            if label == "B"
            else left % modulus + right % modulus >= modulus
        )
        symbols.append(label + str(int(flag)))
        source = (3 * source + 1) // 2 if source & 1 else source // 2
    return tuple(symbols)


@pytest.mark.parametrize("modulus", (3, 7, 49))
@pytest.mark.parametrize(
    "source,ticks",
    ((164, 7), (2174, 13), (26, 5), (19, 4), (2174, 9)),
)
def test_innovation_packet_preserves_the_literal_signed_word(
    source: int, ticks: int, modulus: int
) -> None:
    macro = select_boundary_macro(source, ticks)
    assert macro is not None
    packet = observed_innovation_macro_tape(macro, modulus, ledger=ResourceLedger())
    core = cast(dict[str, object], packet["core"])
    word = (
        cast(tuple[str, ...], packet["entry_symbols"])
        + cast(tuple[str, ...], core["sample"])
        + cast(tuple[str, ...], packet["exit_symbols"])
    )
    expected = _literal_word(source, macro.normalized_symbols, modulus)
    assert word == expected
    totals = cast(dict[str, int], packet["normalized_second_innovation"])
    assert totals["borrow_ones"] == expected.count("B1")
    assert totals["carry_ones"] == expected.count("A1") + expected.count("N1")


def test_pumped_innovation_counts_extend_beyond_the_reported_sample() -> None:
    source = 4 + 40 * (1 << 256)
    macro = select_boundary_macro(source, 388)
    assert macro is not None
    packet = observed_innovation_macro_tape(macro, 7, ledger=ResourceLedger())
    expected = _literal_word(source, macro.normalized_symbols, 7)
    core = cast(dict[str, object], packet["core"])
    assert len(cast(tuple[str, ...], core["sample"])) < len(expected)
    totals = cast(dict[str, int], packet["normalized_second_innovation"])
    assert totals["normalized_steps"] == len(expected)
    assert totals["borrow_ones"] == expected.count("B1")
    assert totals["carry_ones"] == expected.count("A1") + expected.count("N1")


def test_guarded_mixed_macro_is_the_production_action_and_signed_word() -> None:
    ledger = ResourceLedger()
    with BoundaryActionTemplateMemo(ledger) as templates:
        template = templates.get(MixedParityMotif((0, 1)), 64)[0]
        ticks = 64 * 3
        source = next(
            candidate
            for high in range(5, 10)
            if admit_boundary_macro_plan(
                candidate := template.source_residue + (high << template.steps),
                ticks,
            )
            is None
        )
        selected = select_mixed_clock_macro(source, ticks, templates=templates)
        assert selected is not None
        assert selected.motif == (0, 1) and selected.repetitions == 64

    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ledger,
        include_f5=True,
        include_innovation_tape=True,
        innovation_modulus=7,
    )
    expected_word = _literal_word(source, 128, 7)
    assert result.normalized_symbols == 128
    assert result.one_run_symbols == 64
    assert result.phase == 0 and result.physical_ticks == ticks
    assert result.innovation_observation is not None
    assert result.innovation_observation.sample == expected_word[:48]
    assert result.innovation_observation.symbol_counts == tuple(
        expected_word.count(symbol) for symbol in SIGNED_SYMBOLS
    )
    assert result.physical_f5 is not None
    assert result.physical_f5.apply(source) == result.endpoint % 5
    assert ledger.counters["collatz_physical_temporal_mixed_clock_macro_actions"] == 1
