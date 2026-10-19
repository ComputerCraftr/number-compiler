"""Batched normalized digits share authenticated Q19 prefix summaries."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_occurrence import (
    ReversePairOutputOccurrence,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.q19_source_authority import digits_at


def _successor(value: int) -> int:
    return value + int(str(value)[::-1])


def _source196(steps: int) -> int:
    value = 196
    for _ in range(steps):
        value = _successor(value)
    return value


def test_batched_digits_match_individual_reads_in_both_halves(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(_source196(40), 10), base=10)
    try:
        no_growth = owner.initial
        assert no_growth.pair_width == no_growth.output_width
        growth = no_growth
        for _ in range(8):
            if growth.pair_width < growth.output_width:
                break
            growth = owner.apply_pair_step(growth)
        assert growth.pair_width < growth.output_width

        occurrences = (no_growth, growth)
        position_sets = tuple(
            _positions_for(owner, occurrence) for occurrence in occurrences
        )
        expected = tuple(
            tuple(owner.digit(occurrence, position) for position in positions)
            for occurrence, positions in zip(occurrences, position_sets, strict=True)
        )

        def forbidden(*_args: object, **_kwargs: object) -> int:
            raise AssertionError("batch digit read fell back to per-digit API")

        monkeypatch.setattr(ReversePairQ19OutputOwner, "digit", forbidden)
        for occurrence, positions, digits in zip(
            occurrences, position_sets, expected, strict=True
        ):
            assert digits_at(owner, occurrence, positions) == digits
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def _positions_for(
    owner: ReversePairQ19OutputOwner, occurrence: ReversePairOutputOccurrence
) -> tuple[int, ...]:
    width = occurrence.output_width
    half = owner._summaries[occurrence.root].symbols
    candidates = [0, 1, max(0, half - 1), half, min(width - 1, half + 1), width - 1]
    if occurrence.pair_width < width:
        candidates.append(occurrence.pair_width)
    return tuple(dict.fromkeys(candidates))


def test_batched_digits_reject_positions_outside_output() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:
        with pytest.raises(ValueError, match="valid positions"):
            digits_at(owner, owner.initial, (owner.initial.output_width,))
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0
