"""Independent arithmetic and lifetime checks for finite ×5 tile traces."""

from __future__ import annotations

import random

import pytest

from number_compiler.arithmetic.automata.carry_spacetime_trace import Pow5SpatialTrace
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.owned_memo import LedgerReservation


def _packed(value: int) -> tuple[int, int]:
    digits = str(value)
    return int.from_bytes(b"".join(bytes((0, 0, int(d))) for d in digits), "big"), len(
        digits
    )


def _integer(value: int, width: int) -> int:
    digits = value.to_bytes(3 * width, "big")[2::3]
    return int("".join(str(d) for d in digits))


def test_spatial_traces_match_literal_and_carry_across_tile_boundaries() -> None:
    randomizer = random.Random(2626)
    ledger = ResourceLedger()
    with Pow5SpatialTrace(ledger) as owner:
        for _ in range(250):
            value = randomizer.randrange(10 ** randomizer.randrange(1, 30))
            packed, width = _packed(value)
            for row, row_width in owner.issue(packed, width, 4):
                value *= 5
                assert _integer(row, row_width) == value
    assert ledger.nodes == 0
    assert ledger.entries == 0


@pytest.mark.parametrize(
    "packed,width,span", [(10, 1, 1), (1, 2, 1), (1, 1, 5), (-1, 1, 1)]
)
def test_rejects_invalid_inlets(packed: int, width: int, span: int) -> None:
    with Pow5SpatialTrace(ResourceLedger()) as owner:
        with pytest.raises(ValueError):
            owner.issue(packed, width, span)


def test_retirement_failure_revokes_and_retries(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = Pow5SpatialTrace(ledger)
    owner.issue(1, 1, 1)
    original = LedgerReservation.close
    first = True

    def fail_once(reservation: LedgerReservation) -> None:
        nonlocal first
        if first:
            first = False
            raise RuntimeError("injected retirement failure")
        original(reservation)

    monkeypatch.setattr(LedgerReservation, "close", fail_once)
    with pytest.raises(RuntimeError, match="retirement"):
        owner.close()
    with pytest.raises(RuntimeError, match="closed"):
        owner.issue(2, 1, 1)
    owner.close()
    assert ledger.nodes == 0
    assert ledger.entries == 0


def test_capacity_failure_after_fresh_reservation_releases_before_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()

    def refuse(candidate: ResourceLedger, *, nodes: int = 0, entries: int = 0) -> None:
        assert candidate is ledger and nodes == entries == 0
        assert (ledger.nodes, ledger.entries) == (1280, 22)
        raise BlockContextBudgetExceeded("injected capacity refusal")

    with Pow5SpatialTrace(ledger) as owner:
        with monkeypatch.context() as faults:
            faults.setattr(ResourceLedger, "check_capacity", refuse)
            with pytest.raises(BlockContextBudgetExceeded, match="capacity refusal"):
                owner.issue(8, 1, 2)
        assert ledger.nodes == ledger.entries == 0
        rows = owner.issue(8, 1, 2)
        assert tuple(_integer(*row) for row in rows) == (40, 200)
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize("shared_cache", [False, True])
def test_reuse_is_query_owned_and_optional(shared_cache: bool) -> None:
    ledger = ResourceLedger()
    with Pow5SpatialTrace(ledger, shared_cache=shared_cache) as owner:
        first = owner.issue(8, 1, 2)
        second = owner.issue(8, 1, 2)
        assert first == second
        assert (first is second) is shared_cache
        assert ledger.nodes == 1280
    assert ledger.nodes == 0


def test_shared_child_probed_before_convolution_and_halo_is_part_of_key(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    first, width = _packed(123456789012345678901234567890)
    changed_parent, _ = _packed(923456789012345678901234567890)
    changed_halo, _ = _packed(123456789012345678901834567890)
    calls: list[tuple[int, int, int, int]] = []
    forbidden: set[tuple[int, int, int, int]] = set()

    def observe(inlet: int, length: int, below: int, span: int) -> tuple[int, ...]:
        key = (inlet, length, below, span)
        assert key not in forbidden, "shared child was recomputed"
        calls.append(key)
        n = _integer(inlet, length + below)
        below_place, width_place = 10**below, 10**length
        return tuple(
            _packed((n * 5**t // below_place) % width_place)[0]
            for t in range(1, span + 1)
        )

    monkeypatch.setattr(
        "number_compiler.arithmetic.automata.carry_spacetime_trace._trace_leaf", observe
    )
    with Pow5SpatialTrace(ResourceLedger()) as owner:
        owner.issue(first, width, 4)
        previous = set(calls)
        forbidden.update(previous)
        calls.clear()
        rows = owner.issue(changed_parent, width, 4)
        assert previous.isdisjoint(calls)
        assert len(calls) < len(previous)
        assert _integer(*rows[-1]) == 923456789012345678901234567890 * 5**4
        forbidden.clear()
        calls.clear()
        rows = owner.issue(changed_halo, width, 4)
        assert calls
        assert _integer(*rows[-1]) == 123456789012345678901834567890 * 5**4


def test_single_tick_all_adjacent_decimal_cells() -> None:
    with Pow5SpatialTrace(ResourceLedger()) as owner:
        for higher in range(10):
            for lower in range(10):
                decimal = 10 * higher + lower
                packed, width = _packed(decimal)
                result = owner.issue(packed, width, 1)
                assert _integer(*result[0]) == 5 * decimal


def test_failed_tile_construction_preserves_completed_trace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    original, width = _packed(123456789012345678901234567890)
    different, _ = _packed(923456789012345678901234567890)
    with Pow5SpatialTrace(ledger) as owner:
        completed = owner.issue(original, width, 4)
        retained = (ledger.nodes, ledger.entries)

        def fail_tile(*_args: int) -> tuple[int, ...]:
            raise RuntimeError("injected tile failure")

        with monkeypatch.context() as faults:
            faults.setattr(
                "number_compiler.arithmetic.automata.carry_spacetime_trace._trace_leaf",
                fail_tile,
            )
            with pytest.raises(RuntimeError, match="injected tile failure"):
                owner.issue(different, width, 4)
            assert owner.issue(original, width, 4) is completed
            assert (ledger.nodes, ledger.entries) == retained
    assert ledger.nodes == ledger.entries == 0
