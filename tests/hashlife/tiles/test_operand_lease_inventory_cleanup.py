"""Exact, retryable release of retained boundary operand views."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_result_leases import ResultLease
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileArena, TileLease
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict
from tests.support.ledger_failures import inject_release_failure
from tests.support.tile_results import incoming_setup


def _publish_with_operand() -> tuple[
    ResourceLedger,
    TileArena,
    CompletedResultArena,
    TileLease,
    TileLease,
    tuple[TileLease, BoundaryTileView, ResultLease],
]:
    ledger, _, tiles, results, source, output, key, result, boundary = incoming_setup()
    view = BoundaryTileView(boundary.tile, 0, 1)
    result = replace(
        result,
        outgoing_boundaries=BoundaryTileOperands(view, None),
    )
    lease = results.publish(key, result)
    return ledger, tiles, results, source, output, (boundary, view, lease)


@pytest.mark.parametrize("failure_timing", ("before", "after"))
@pytest.mark.parametrize("retry_via_arena", (False, True))
def test_result_lease_retries_exact_operand_release(
    monkeypatch: pytest.MonkeyPatch,
    failure_timing: str,
    retry_via_arena: bool,
) -> None:
    ledger, _tiles, results, source, output, payload = _publish_with_operand()
    boundary, _view, lease = payload
    inventory = results._leased_boundary_operands
    owner = inventory.owner
    with monkeypatch.context() as patch:
        inject_release_failure(
            patch, ledger, owner, entries=1, after_apply=failure_timing == "after"
        )
        with pytest.raises(RuntimeError, match="injected ledger release failure"):
            lease.close()

    assert lease._operand_map_released is True
    assert not inventory.records
    expected_pending = int(failure_timing == "before")
    assert inventory.pending_release_entries == expected_pending
    inventory_owner = next(item for item in ledger.inventory() if item.owner == owner)
    assert inventory_owner.entries == len(inventory.records) + expected_pending
    assert inventory_owner.observed_entries == len(inventory.records)

    if retry_via_arena:
        results.clear()
        assert inventory.pending_release_entries == 0
    lease.close()
    assert lease._closed is True
    assert inventory.pending_release_entries == 0
    assert ledger._account(owner).entries == 0
    boundary.close()
    output.close()
    source.close()


def test_retrying_one_operand_release_does_not_consume_another_lease(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, results, source, output, payload = _publish_with_operand()
    boundary, view, first = payload
    inventory = results._leased_boundary_operands
    first.close()
    other_boundary, other_view = _additional_operand(tiles, output)
    inventory.acquire((view, other_view))
    inventory.acquire((view,))
    owner = inventory.owner
    original_release = ledger.release
    fail_once = True

    def fail_release(target: int, entries: int = 0, nodes: int = 0) -> None:
        nonlocal fail_once
        if target == owner and entries == 1 and fail_once:
            fail_once = False
            raise RuntimeError("injected release failure")
        original_release(target, entries, nodes)

    with monkeypatch.context() as patch:
        patch.setattr(ledger, "release", fail_release)
        with pytest.raises(RuntimeError, match="injected release failure"):
            inventory.release((view, other_view))

    assert inventory.records[view] == 1
    assert inventory.pending_release_entries == 1
    inventory.release((view,))
    assert not inventory.records
    inventory.retry_release()
    assert ledger._account(owner).entries == 0
    other_boundary.close()
    boundary.close()
    output.close()
    source.close()


def test_failed_operand_acquire_retries_its_reserved_ledger_entries(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _tiles, results, source, output, payload = _publish_with_operand()
    boundary, first_view, lease = payload
    lease.close()
    other_boundary, second_view = _additional_operand(_tiles, output)
    inventory = results._leased_boundary_operands
    owner = inventory.owner
    set_item = LedgerDict.__setitem__
    fail_once = True

    def fail_second_insert(
        records: LedgerDict[BoundaryTileView, int],
        view: BoundaryTileView,
        count: int,
    ) -> None:
        nonlocal fail_once
        if records is inventory.records and view is second_view and fail_once:
            fail_once = False
            raise RuntimeError("injected operand insert failure")
        set_item(records, view, count)

    release = ledger.release
    fail_release = True

    def fail_release_before_apply(
        target: int,
        entries: int = 0,
        nodes: int = 0,
    ) -> None:
        nonlocal fail_release
        if target == owner and entries == 2 and fail_release:
            fail_release = False
            raise RuntimeError("injected reservation release failure")
        release(target, entries, nodes)

    with monkeypatch.context() as patch:
        patch.setattr(LedgerDict, "__setitem__", fail_second_insert)
        patch.setattr(ledger, "release", fail_release_before_apply)
        with pytest.raises(RuntimeError, match="injected reservation release failure"):
            inventory.acquire((first_view, second_view))

    assert not inventory.records
    assert inventory.pending_release_entries == 2
    assert ledger._account(owner).entries == 2
    inventory.retry_release()
    assert ledger._account(owner).entries == 0
    assert inventory.pending_release_entries == 0
    other_boundary.close()
    boundary.close()
    output.close()
    source.close()


def _additional_operand(
    tiles: TileArena, output: TileLease
) -> tuple[TileLease, BoundaryTileView]:
    boundary = tiles.leaf(tiles.resolve(output.tile).alphabet, 0)
    return boundary, BoundaryTileView(boundary.tile, 0, 1)
