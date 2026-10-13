"""Guarded observation words agree with an independent normalized orbit."""

from typing import cast

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.boundary_macros import select_boundary_macro
from number_compiler.sequences.collatz.innovation_temporal_tape import (
    observed_innovation_macro_tape,
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
