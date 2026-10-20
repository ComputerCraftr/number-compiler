"""Failure-path checks for completed-result and causal tile lease cleanup."""

from __future__ import annotations

from collections.abc import Callable, Iterable
from dataclasses import replace
from typing import Literal, cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_result_acquisition import (
    ResultAcquisitionLeaseOwner,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    CompletedResult,
    PoweredResultKey,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerList
from tests.support.private_attributes import private_test_attribute
from tests.support.tile_kernel import make_tile_runtime
from tests.support.tile_results import incoming_setup, setup_tile_results


def _lease_flag(lease: object, field: str) -> bool:
    """Inspect a lease state bit in a deliberately adversarial cleanup test."""
    value = object.__getattribute__(lease, field)
    if type(value) is not bool:
        raise AssertionError(f"lease field {field} is not boolean")
    return value


@pytest.mark.parametrize(
    "callback_name",
    (
        "signature_validator",
        "input_validator",
        "output_validator",
        "fused_action_validator",
        "fused_wiring_validator",
    ),
)
def test_result_authority_rejects_replaced_validator(
    monkeypatch: pytest.MonkeyPatch, callback_name: str
) -> None:
    _, _, _, results, source, output, _, _ = setup_tile_results()

    def replacement(*_args: object) -> None:
        raise AssertionError("a replaced validator must not be called")

    try:
        authority = results.validated_action_authority()
        with monkeypatch.context() as patch:
            patch.setattr(results, callback_name, replacement)
            with pytest.raises(ValueError, match="authority changed"):
                results.validated_action_authority()
        assert results.validated_action_authority() is authority
    finally:
        output.close()
        source.close()


def _published_with_boundary(
    side: Literal["left", "right"],
) -> tuple[
    ResourceLedger,
    TileArena,
    CompletedResultArena,
    TileLease,
    TileLease,
    TileLease,
    PoweredResultKey,
    CompletedResult,
]:
    ledger, _, tiles, results, source, output, key, result, boundary = incoming_setup()
    if side == "left":
        operands = BoundaryTileOperands(
            BoundaryTileView(boundary.tile, 0, 1),
            None,
        )
    else:
        operands = BoundaryTileOperands(
            None,
            BoundaryTileView(boundary.tile, 0, 1),
        )
    outgoing = replace(result, outgoing_boundaries=operands)
    return ledger, tiles, results, source, output, boundary, key, outgoing


def test_result_lease_cleanup_closes_dependencies_before_output(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _tiles, results, source, output, boundary, key, outgoing = (
        _published_with_boundary("right")
    )
    held = results.publish(key, outgoing)
    held_snapshot = held.audit_snapshot()
    boundary_ids = tuple(
        lease.audit_snapshot().identity for lease in held_snapshot.boundary_tiles
    )
    output_id = held_snapshot.tile.audit_snapshot().identity
    events: list[tuple[str, int]] = []

    with monkeypatch.context() as patch:
        close_tile = TileLease.close
        release_boundary = results.release_boundary_leases

        def tracked_close(lease: TileLease) -> None:
            identity = lease.audit_snapshot().identity
            if identity in boundary_ids or identity == output_id:
                events.append(("tile", identity))
            close_tile(lease)

        def tracked_accounting(
            count: int,
            operand_views: tuple[BoundaryTileView, ...],
            *,
            operands_already_mutated: bool = False,
            on_operands_mutated: Callable[[], object] | None = None,
        ) -> None:
            events.append(("account", count))
            release_boundary(
                count,
                operand_views,
                operands_already_mutated=operands_already_mutated,
                on_operands_mutated=on_operands_mutated,
            )

        patch.setattr(TileLease, "close", tracked_close)
        patch.setattr(results, "release_boundary_leases", tracked_accounting)
        held.close()

    expected = [
        *(("tile", lease_id) for lease_id in reversed(boundary_ids)),
        ("account", len(boundary_ids)),
        ("tile", output_id),
        ("account", 0),
    ]
    assert events == expected
    boundary.close()
    output.close()
    source.close()


def test_result_lease_rejects_binding_change_after_partial_close(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _, _, results, source, output, key, result = setup_tile_results()
    held = results.publish(key, result)
    release_boundary = results.release_boundary_leases
    fail_once = True

    def fail_operand_release(
        count: int,
        operand_views: tuple[BoundaryTileView, ...],
        *,
        operands_already_mutated: bool = False,
        on_operands_mutated: Callable[[], object] | None = None,
    ) -> None:
        nonlocal fail_once
        if count == 0 and fail_once:
            fail_once = False
            raise RuntimeError("injected operand release failure")
        release_boundary(
            count,
            operand_views,
            operands_already_mutated=operands_already_mutated,
            on_operands_mutated=on_operands_mutated,
        )

    monkeypatch.setattr(results, "release_boundary_leases", fail_operand_release)
    with pytest.raises(RuntimeError, match="injected operand release failure"):
        held.close()
    assert _lease_flag(held, "_closing") is True
    assert _lease_flag(held, "_output_closed") is True
    assert held.audit_snapshot().closed is False

    original_tile = held.audit_snapshot().tile
    object.__setattr__(held, "_tile", source)
    with pytest.raises(ValueError, match="cleanup binding changed"):
        held.close()
    assert source.audit_snapshot().closed is False
    object.__setattr__(held, "_tile", original_tile)

    held.close()
    assert held.audit_snapshot().closed is True
    output.close()
    source.close()


def test_result_arena_clear_retries_unpublished_acquisition_lease(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, results, source, output, boundary, key, outgoing = (
        _published_with_boundary("left")
    )
    original_acquire = tiles.acquire_reserved
    acquired: list[TileLease] = []
    calls = 0

    def fail_second_acquisition(tile: TileID) -> TileLease:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise RuntimeError("injected second tile acquisition failure")
        lease = original_acquire(tile)
        acquired.append(lease)
        return lease

    original_close = TileLease.close
    close_failed = False

    def fail_first_rollback_close(lease: TileLease) -> None:
        nonlocal close_failed
        if acquired and lease is acquired[0] and not close_failed:
            close_failed = True
            raise RuntimeError("injected rollback close failure")
        original_close(lease)

    with monkeypatch.context() as patch:
        patch.setattr(tiles, "acquire_reserved", fail_second_acquisition)
        patch.setattr(TileLease, "close", fail_first_rollback_close)
        with pytest.raises(RuntimeError, match="injected rollback close failure"):
            results.publish(key, outgoing)

    pending = tuple(
        record
        for record in results.audit_snapshot().pending_records
        if type(record) is TileLease
    )
    assert len(pending) == 1
    pending_lease = pending[0]
    assert pending_lease is acquired[0]
    assert pending_lease.audit_snapshot().closed is False

    results.clear()
    assert not results.audit_snapshot().pending_records
    assert pending_lease.audit_snapshot().closed is True
    boundary.close()
    output.close()
    source.close()


def test_causal_workspace_teardown_attempts_later_roots_and_retries_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    engine = CausalTileEngine(scheduler)
    first = tiles.leaf(adapter.alphabet(action), 0)
    failing = tiles.leaf(adapter.alphabet(action), 1)
    engine.lease_workspace.tiles.extend((first, failing))
    close_order: list[int | str] = []
    original_close = TileLease.close
    fail_once = True

    def fail_then_close(lease: TileLease) -> None:
        nonlocal fail_once
        close_order.append(lease.audit_snapshot().identity)
        if lease is failing and fail_once:
            fail_once = False
            raise RuntimeError("injected root close failure")
        original_close(lease)

    workspace = scheduler.causal_workspace
    tasks = scheduler.causal_tasks
    workspace_clear = workspace.clear
    tasks_clear = tasks.clear

    def record_workspace_clear() -> None:
        close_order.append("workspace")
        workspace_clear()

    def record_tasks_clear() -> None:
        close_order.append("tasks")
        tasks_clear()

    with monkeypatch.context() as patch:
        patch.setattr(TileLease, "close", fail_then_close)
        patch.setattr(workspace, "clear", record_workspace_clear)
        patch.setattr(tasks, "clear", record_tasks_clear)
        with pytest.raises(RuntimeError, match="injected root close failure"):
            engine.release_workspace()

    assert close_order[:2] == [
        failing.audit_snapshot().identity,
        first.audit_snapshot().identity,
    ]
    assert "workspace" in close_order and "tasks" in close_order
    assert first.audit_snapshot().closed is True
    assert failing.audit_snapshot().closed is False
    assert engine.lease_workspace.tiles == [failing]

    engine.release_workspace()
    assert failing.audit_snapshot().closed is True
    assert not engine.lease_workspace.tiles


def test_acquisition_restore_releases_unwritten_cleanup_reservations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _, _, results, source, output, _, _ = setup_tile_results()
    owner_value: object = object.__getattribute__(results, "_lease_acquisitions")
    if type(owner_value) is not ResultAcquisitionLeaseOwner:
        raise AssertionError("result acquisition owner has an unexpected type")
    owner = owner_value
    extend = cast(
        Callable[
            [LedgerList[TileLease | int | None], Iterable[TileLease | int | None]],
            None,
        ],
        private_test_attribute(LedgerList, "extend"),
    )

    def append_one_then_fail(
        store: LedgerList[TileLease | int | None],
        values: Iterable[TileLease | int | None],
    ) -> None:
        if id(store) == results.audit_snapshot().pending_acquisitions_store_identity:
            store.append(next(iter(values)))
            raise RuntimeError("injected partial cleanup restore")
        extend(store, values)

    with monkeypatch.context() as patch:
        patch.setattr(LedgerList, "extend", append_one_then_fail)
        with pytest.raises(RuntimeError, match="partial cleanup restore"):
            restore_leases = cast(
                Callable[[list[TileLease]], None],
                object.__getattribute__(owner, "_restore_leases"),
            )
            restore_leases([source, output])

    assert owner.clear_entries == owner.clear_nodes == 1
    owner.retry()
    close_unrecorded = cast(
        Callable[[list[TileLease]], None],
        object.__getattribute__(owner, "_close_unrecorded"),
    )
    close_unrecorded([source, output])
    account = ledger.account_status(owner.owner)
    assert account.entries == account.nodes == 0
    assert not owner.records
    assert source.audit_snapshot().closed and output.audit_snapshot().closed
