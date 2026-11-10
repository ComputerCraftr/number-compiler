"""Source-authenticated large packed T² cones; no period or external carry guess."""

from __future__ import annotations

from collections.abc import Iterator
from typing import NamedTuple

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import double_reverse as metric_keys
from number_compiler.resources.owned_memo import LedgerReservation
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_carry_spacetime import (
    try_source_bound_square_cone,
)
from number_compiler.sequences.double_reverse.temporal_packed_diagonal import (
    TemporalSquareScratchReservation,
    TemporalSquareStats,
    publish_packed_diagonal,
)


class _PackedWorkspace(NamedTuple):
    ledger: ResourceLedger
    arena: LedgerSLPArena
    scratch_owner: int


@pytest.fixture
def packed_workspace() -> Iterator[_PackedWorkspace]:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "large-packed-test", "double_reverse_test")
    scratch_owner = ledger.register("large-packed-scratch", "workspace")
    try:
        yield _PackedWorkspace(ledger, arena, scratch_owner)
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(scratch_owner)


def _literal(seed: int, steps: int) -> int:
    """Independent LSD-first decimal oracle without full-integer divmod loops."""
    digits: list[int] = []
    remaining = seed
    while remaining:
        remaining, digit = divmod(remaining, 10)
        digits.append(digit)
    if not digits:
        digits.append(0)
    for _ in range(steps):
        carry = 0
        doubled_reversal: list[int] = []
        for digit in reversed(digits):
            doubled = 2 * digit + carry
            carry, output_digit = divmod(doubled, 10)
            doubled_reversal.append(output_digit)
        if carry:
            doubled_reversal.append(carry)
        while len(doubled_reversal) > 1 and doubled_reversal[-1] == 0:
            doubled_reversal.pop()
        digits = doubled_reversal

    result = 0
    for digit in reversed(digits):
        result = 10 * result + digit
    return result


def _scalar_reference(seed: int, steps: int) -> int:
    value = seed
    for _ in range(steps):
        reversed_value = 0
        while value:
            value, digit = divmod(value, 10)
            reversed_value = 10 * reversed_value + digit
        value = 2 * reversed_value
    return value


@pytest.mark.parametrize("seed", (0, 1, 196, 99999))
@pytest.mark.parametrize("steps", range(9))
def test_digit_oracle_matches_scalar_recurrence(seed: int, steps: int) -> None:
    assert _literal(seed, steps) == _scalar_reference(seed, steps)


@pytest.mark.parametrize("seed,steps", [(196, 8192), (168, 8192), (196, 10000)])
def test_cold_large_packed_endpoint_matches_exact_scalar(seed: int, steps: int) -> None:
    with DoubleReverseTerm(seed, steps, max_steps=steps, max_state_bits=100000) as term:
        assert term.materialize(max_bits=100000) == _literal(seed, steps)
        counters = term.metrics()
        assert counters["double_reverse_packed_diagonal_row_evaluations"] >= 2048
        assert counters["double_reverse_temporal_hashlife_publications"] > 0


def test_large_packed_respects_local_scratch_budget(
    packed_workspace: _PackedWorkspace,
) -> None:
    ledger, arena, scratch_owner = packed_workspace
    source = arena.repeat(arena.terminal(2), 4 * 2048)
    before_nodes = len(arena.nodes)
    ledger.tighten_limits(
        max_nodes=ledger.nodes + 4,
        max_cache_entries=ledger.entries + 4,
    )
    assert try_source_bound_square_cone(arena, source, 2048, scratch_owner) is None
    _assert_rolled_back(packed_workspace, before_nodes)


def test_large_packed_beyond_guard_declines_without_side_effects(
    packed_workspace: _PackedWorkspace,
) -> None:
    _ledger, arena, scratch_owner = packed_workspace
    root = arena.word((1, 9, 6))
    before = len(arena.nodes)
    assert try_source_bound_square_cone(arena, root, 32768, scratch_owner) is None
    assert len(arena.nodes) == before


def test_large_packed_rejects_invalid_source_and_scratch_authority(
    packed_workspace: _PackedWorkspace,
) -> None:
    _ledger, arena, scratch_owner = packed_workspace
    root = arena.word((1, 9, 6))
    with pytest.raises(ValueError, match="complete causal halo"):
        try_source_bound_square_cone(arena, root, 2048, scratch_owner)
    complete = arena.repeat(arena.terminal(3), 4 * 2048)
    before_scratch_check = len(arena.nodes)
    with pytest.raises(ValueError, match="scratch owner"):
        try_source_bound_square_cone(arena, complete, 2048, True)
    assert len(arena.nodes) == before_scratch_check


def test_large_packed_rejects_released_source_arena(
    packed_workspace: _PackedWorkspace,
) -> None:
    _ledger, arena, scratch_owner = packed_workspace
    root = arena.repeat(arena.terminal(3), 4 * 2048)
    arena.dispose()
    with pytest.raises(ValueError, match="disposed ledgered SLP arena"):
        try_source_bound_square_cone(arena, root, 2048, scratch_owner)


def test_large_packed_accounting_failure_rolls_back_output(
    monkeypatch: pytest.MonkeyPatch,
    packed_workspace: _PackedWorkspace,
) -> None:
    _ledger, arena, scratch_owner = packed_workspace
    source = arena.repeat(arena.word((1, 4, 8, 9)), 2048)
    checkpoint = len(arena.nodes)

    original_bump = ResourceLedger.bump

    def fail_region_accounting(
        resource_ledger: ResourceLedger, counter: str, amount: int = 1
    ) -> None:
        if counter == metric_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_REGION_VISITS:
            raise RuntimeError("injected work accounting failure")
        original_bump(resource_ledger, counter, amount)

    monkeypatch.setattr(ResourceLedger, "bump", fail_region_accounting)
    with pytest.raises(RuntimeError, match="work accounting"):
        try_source_bound_square_cone(arena, source, 2048, scratch_owner)
    _assert_rolled_back(packed_workspace, checkpoint)


def test_large_packed_release_failure_rolls_back_output(
    monkeypatch: pytest.MonkeyPatch,
    packed_workspace: _PackedWorkspace,
) -> None:
    _ledger, arena, scratch_owner = packed_workspace
    source = arena.repeat(arena.word((2, 3, 7, 9)), 2048)
    checkpoint = len(arena.nodes)
    original_close = ResourceLedger.close_reservation

    def close_then_fail(
        resource_ledger: ResourceLedger, reservation: LedgerReservation
    ) -> None:
        original_close(resource_ledger, reservation)
        raise RuntimeError("injected scratch release failure")

    monkeypatch.setattr(ResourceLedger, "close_reservation", close_then_fail)
    with pytest.raises(RuntimeError, match="scratch release"):
        try_source_bound_square_cone(arena, source, 2048, scratch_owner)
    _assert_rolled_back(packed_workspace, checkpoint)


def test_failed_output_publication_counts_only_consumed_digits(
    monkeypatch: pytest.MonkeyPatch,
    packed_workspace: _PackedWorkspace,
) -> None:
    ledger, arena, scratch_owner = packed_workspace
    source = arena.repeat(arena.terminal(4), 4 * 64)
    checkpoint = len(arena.nodes)
    stats = TemporalSquareStats(0, 0, 0, 0, 0)
    original_terminal = LedgerSLPArena.terminal
    terminal_calls = 0

    def fail_after_two_terminals(owner: LedgerSLPArena, symbol: int) -> int:
        nonlocal terminal_calls
        if terminal_calls == 2:
            raise RuntimeError("injected partial packed output publication")
        terminal_calls += 1
        return original_terminal(owner, symbol)

    monkeypatch.setattr(LedgerSLPArena, "terminal", fail_after_two_terminals)
    reservation = LedgerReservation(ledger, scratch_owner)
    with pytest.raises(RuntimeError, match="partial packed output"):
        with TemporalSquareScratchReservation(reservation) as workspace:
            publish_packed_diagonal(arena, source, 64, workspace, None, stats)

    assert len(arena.nodes) == checkpoint
    assert terminal_calls == 2
    assert stats.packed_output_digit_visits == 2 * (2 * 64) + 3
    account = next(item for item in ledger.inventory() if item.owner == scratch_owner)
    assert account.nodes == account.entries == 0


def _assert_rolled_back(workspace: _PackedWorkspace, checkpoint: int) -> None:
    assert len(workspace.arena.nodes) == checkpoint
    account = next(
        item
        for item in workspace.ledger.inventory()
        if item.owner == workspace.scratch_owner
    )
    assert account.nodes == account.entries == 0
