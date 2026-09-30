"""Canonical source-root summaries used by the first-event Collatz shortcut."""

from __future__ import annotations

from tests.support.tile_kernel import _runtime_source
import pytest

from number_compiler.hashlife.tiles.source_root_match_memo import source_root_match
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


@pytest.mark.parametrize(
    ("digits", "phase0", "phase1"),
    (
        ((1, 0, 1, 0), None, 0),
        ((1, 0, 0, 0), 2, 0),
        ((0, 1, 0, 1), 0, None),
    ),
)
def test_source_root_match_composes_both_alternating_phases(
    digits: tuple[int, ...], phase0: int | None, phase1: int | None
) -> None:
    _ledger, tiles, adapter, action, scheduler, source = _runtime_source(
        CollatzPhysicalBlockEffect(), digits
    )
    try:
        result = source_root_match(scheduler.results, source.tile)
        assert result.phase0_first_mismatch == phase0
        assert result.phase1_first_mismatch == phase1
    finally:
        source.close()


def test_source_root_match_reuses_the_parent_before_child_work() -> None:
    ledger, tiles, adapter, action, scheduler, source = _runtime_source(
        CollatzPhysicalBlockEffect(), (1, 0, 1, 0, 1, 0, 0, 0)
    )
    try:
        expected = source_root_match(scheduler.results, source.tile)
        evaluations = ledger.counters["collatz_source_root_match_evaluations"]
        assert source_root_match(scheduler.results, source.tile) == expected
        assert ledger.counters["collatz_source_root_match_evaluations"] == evaluations
        assert ledger.counters["collatz_source_root_match_early_hits"] > 0
    finally:
        source.close()
