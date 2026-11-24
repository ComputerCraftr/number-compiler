"""Exact H actions on certified repeated blocks and their seams."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.temporal_cone import (
    CarrySpacetimePower,
    TemporalSquareScratchCapacityRefused,
    TemporalSquareScratchReservation,
)
from number_compiler.arithmetic.carry.reflected_h_power import padded_h_cell
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.owned_memo import LedgerReservation


@pytest.mark.parametrize("multiplier", (2, 5))
@pytest.mark.parametrize("fringe", (((), ()), ((7, 3, 9, 51, 4), (24, 72, 0))))
def test_periodic_block_actions_keep_ordered_seams(
    multiplier: int, fringe: tuple[tuple[int, ...], tuple[int, ...]]
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("cyclic-h-test", "scratch")
    arena = LedgerSLPArena(ledger, "cyclic-h-test", "grammar")
    prefix, suffix = fringe
    motif = (11, 64, 27)
    source = prefix + motif * 96 + suffix
    try:
        root = arena.concat_many(
            (
                arena.word(prefix),
                arena.repeat(arena.word(motif), 96),
                arena.word(suffix),
            )
        )
        with TemporalSquareScratchReservation(
            LedgerReservation(ledger, owner)
        ) as scratch:
            bank = CarrySpacetimePower(
                scratch,
                None,
                None,
                cell_action=lambda a, b: padded_h_cell(a, b, multiplier),
            )
            try:
                result = bank.advance_blocks_slp(arena, root, 8)
                expected = bank.advance_blocks(source, 8)
                assert arena.materialize(result) == expected
                result2 = bank.advance_blocks_slp(arena, result, 4)
                assert arena.materialize(result2) == bank.advance_blocks(expected, 4)
            finally:
                bank.release_temporary_storage()
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


@pytest.mark.parametrize("multiplier", (2, 5))
def test_long_odd_period_issues_only_phase_and_boundary_actions(
    multiplier: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("cyclic-h-long", "scratch")
    arena = LedgerSLPArena(ledger, "cyclic-h-long", "grammar")
    calls = 0
    original = CarrySpacetimePower.publish

    def counted(self: CarrySpacetimePower, target: LedgerSLPArena, tile: int) -> int:
        nonlocal calls
        calls += 1
        return original(self, target, tile)

    monkeypatch.setattr(CarrySpacetimePower, "publish", counted)
    try:
        root = arena.repeat(arena.word((13, 47, 52)), 32768)
        with TemporalSquareScratchReservation(
            LedgerReservation(ledger, owner)
        ) as scratch:
            bank = CarrySpacetimePower(
                scratch,
                None,
                None,
                cell_action=lambda a, b: padded_h_cell(a, b, multiplier),
            )
            try:
                output = bank.advance_blocks_slp(arena, root, 64)
                assert arena.nodes[output].length == 98304 + 64
                assert calls == 5
            finally:
                bank.release_temporary_storage()
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


def test_failed_periodic_publication_rolls_back(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("cyclic-h-failure", "scratch")
    arena = LedgerSLPArena(ledger, "cyclic-h-failure", "grammar")
    try:
        root = arena.repeat(arena.word((12, 30, 45)), 256)
        checkpoint = len(arena.nodes)

        def fail(_self: CarrySpacetimePower, _arena: LedgerSLPArena, _tile: int) -> int:
            raise RuntimeError("injected periodic publication failure")

        monkeypatch.setattr(CarrySpacetimePower, "publish", fail)
        with TemporalSquareScratchReservation(
            LedgerReservation(ledger, owner)
        ) as scratch:
            bank = CarrySpacetimePower(
                scratch, None, None, cell_action=lambda a, b: padded_h_cell(a, b, 5)
            )
            try:
                with pytest.raises(RuntimeError, match="injected periodic"):
                    bank.advance_blocks_slp(arena, root, 8)
                assert len(arena.nodes) == checkpoint
            finally:
                bank.release_temporary_storage()
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


def test_periodic_interval_capacity_refusal_falls_back_exactly(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("cyclic-h-capacity", "scratch")
    arena = LedgerSLPArena(ledger, "cyclic-h-capacity", "grammar")
    source = (12, 30, 45) * 100
    try:
        root = arena.repeat(arena.word((12, 30, 45)), 100)
        original = TemporalSquareScratchReservation.acquire
        original_publish = CarrySpacetimePower.publish
        refused = False
        published = 0

        def track_publish(
            self: CarrySpacetimePower, target: LedgerSLPArena, tile: int
        ) -> int:
            nonlocal published
            published += 1
            return original_publish(self, target, tile)

        def fail_once(
            self: TemporalSquareScratchReservation, entries: int = 1, nodes: int = 1
        ) -> None:
            nonlocal refused
            if entries == 3 * len(arena.nodes) and published and not refused:
                refused = True
                raise TemporalSquareScratchCapacityRefused("injected interval capacity")
            original(self, entries, nodes)

        monkeypatch.setattr(TemporalSquareScratchReservation, "acquire", fail_once)
        monkeypatch.setattr(CarrySpacetimePower, "publish", track_publish)
        with TemporalSquareScratchReservation(
            LedgerReservation(ledger, owner)
        ) as scratch:
            bank = CarrySpacetimePower(
                scratch, None, None, cell_action=lambda a, b: padded_h_cell(a, b, 5)
            )
            try:
                result = bank.advance_blocks_slp(arena, root, 8)
                assert refused
                assert arena.materialize(result) == bank.advance_blocks(source, 8)
            finally:
                bank.release_temporary_storage()
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)
