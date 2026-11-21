"""Chronological all-inlet signal composition over compressed words."""

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.periodic_slp import periodic_word
from number_compiler.arithmetic.carry.temporal_signal import TemporalSignalBank
from number_compiler.resources.ledger import ResourceLedger


def test_stateful_same_time_events_match_literal_and_warm_root(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("signal-test-scratch", "workspace")
    arena = LedgerSLPArena(ledger, "signal-test", "arithmetic")
    # Each tuple is (next state, event bits) for inlets zero and one.
    law = (((1, 1), (0, 2)), ((0, 3), (1, 1)), ((1, 0), (0, 3)))
    bank = TemporalSignalBank(arena, scratch, law, 3)
    try:
        period = (0, 1, 2)
        root = periodic_word(arena, period, 101, phase=1)
        expected: list[int | None] = []
        for inlet in (0, 1):
            state = inlet
            first = None
            for index in range(101):
                state, events = law[period[(index + 1) % 3]][state]
                if events == 3 and first is None:
                    first = index
            expected.append(first)
        assert [bank.first_simultaneous(root, i) for i in (0, 1)] == expected

        def poisoned(*_args: object) -> None:
            raise AssertionError("warm signal rediscovered children")

        monkeypatch.setattr(TemporalSignalBank, "_then", poisoned)
        assert bank.first_simultaneous(root, 0) == expected[0]
    finally:
        bank.dispose()
        arena.dispose()
        ledger.mark_disposed(scratch)
    assert ledger.entries == ledger.nodes == 0


def test_signal_rejects_arena_rollback() -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("signal-stale-scratch", "workspace")
    arena = LedgerSLPArena(ledger, "signal-stale", "arithmetic")
    bank = TemporalSignalBank(arena, scratch, (((0, 1),),), 1)
    try:
        checkpoint = len(arena.nodes)
        root = arena.terminal(0)
        assert bank.first_simultaneous(root, 0) == 0
        arena.rollback_unpublished_suffix(checkpoint)
        with pytest.raises(ValueError, match="stale"):
            bank.first_simultaneous(root, 0)
    finally:
        bank.dispose()
        arena.dispose()
        ledger.mark_disposed(scratch)


def test_small_signal_does_not_reserve_the_whole_arena() -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("signal-large-arena-scratch", "workspace")
    arena = LedgerSLPArena(ledger, "signal-large-arena", "arithmetic")
    for symbol in range(1000):
        arena.terminal(symbol)
    bank = TemporalSignalBank(arena, scratch, (((0, 1),),), 1)
    try:
        ledger.tighten_limits(max_nodes=ledger.nodes + 50, max_cache_entries=None)
        assert bank.first_simultaneous(arena.terminal(0), 0) == 0
    finally:
        bank.dispose()
        arena.dispose()
        ledger.mark_disposed(scratch)
