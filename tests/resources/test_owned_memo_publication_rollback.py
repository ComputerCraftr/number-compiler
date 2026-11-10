"""Failed memo writes remove only their attempted ledger-owned row."""

from __future__ import annotations

from collections.abc import Callable
from types import FrameType, TracebackType

import pytest

from number_compiler.resources.ledger import (
    LedgerReservation,
    OwnedMemo,
    ResourceLedger,
)
from number_compiler.resources.stores import LedgerDict


def _owned_memo_write_frame(
    error: BaseException, *, operation: str = "__setitem__"
) -> FrameType:
    traceback: TracebackType | None = error.__traceback__
    while traceback is not None:
        frame = traceback.tb_frame
        if frame.f_code.co_name == operation and frame.f_code.co_filename.endswith(
            "resources/owned_memo.py"
        ):
            return frame
        traceback = traceback.tb_next
    raise AssertionError("retained error has no OwnedMemo write frame")


def test_new_memo_write_rolls_back_exact_row_and_reconciles_release_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("memo-publication", "ACTION_PROGRAM")
    memo: OwnedMemo[str, object] = OwnedMemo(ledger, owner, nodes_per_entry=1)
    store = memo.audit_snapshot().container
    payload = object()
    publication_error = RuntimeError("injected failure after memo insert")
    first_release_error = RuntimeError("injected release failure")
    original_setitem: Callable[[LedgerDict[object, object], object, object], None] = (
        LedgerDict[object, object].__setitem__
    )
    original_release = ledger.release
    mutation_calls = 0
    release_failures = [first_release_error]

    def fail_delete_mutation() -> None:
        nonlocal mutation_calls
        mutation_calls += 1
        if mutation_calls == 2:
            raise RuntimeError("injected delete callback failure")

    def insert_then_fail(
        mapping: LedgerDict[object, object], key: object, value: object
    ) -> None:
        original_setitem(mapping, key, value)
        if mapping is store and key == "payload":
            value = None
            raise publication_error

    def fail_release(owner_id: int, *, entries: int = 0, nodes: int = 0) -> None:
        if owner_id == owner and entries == 1 and nodes == 1 and release_failures:
            raise release_failures.pop(0)
        original_release(owner_id, entries=entries, nodes=nodes)

    monkeypatch.setattr(ledger, "note_store_mutation", fail_delete_mutation)
    monkeypatch.setattr(LedgerDict, "__setitem__", insert_then_fail)
    monkeypatch.setattr(ledger, "release", fail_release)
    try:
        with pytest.raises(RuntimeError, match="after memo insert") as captured:
            memo["payload"] = payload

        assert captured.value is publication_error
        assert captured.value.__cause__ is first_release_error
        assert mutation_calls == 2
        assert len(memo) == 0
        assert ledger.account_usage(owner) == (1, 1)
        assert memo.audit_snapshot().pending_clear_entries == 1
        frame = _owned_memo_write_frame(captured.value)
        assert frame.f_locals["value"] is not payload
        assert frame.f_locals["stored_value"] is not payload
    finally:
        monkeypatch.undo()
        try:
            memo.clear()
        finally:
            memo.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_reserved_dynamic_memo_write_uses_exact_store_rollback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = ledger.register("memo-reservation", "WORKSPACE")
    target = ledger.register("memo-dynamic-target", "ACTION_PROGRAM")
    reservation = LedgerReservation(ledger, source)
    reservation.reserve(entries=1, nodes=3)
    memo: OwnedMemo[str, tuple[int, ...]] = OwnedMemo(
        ledger, target, node_cost=lambda _key, value: len(value)
    )
    store = memo.audit_snapshot().container
    publication_error = KeyboardInterrupt("injected post-insert interrupt")
    original_setitem: Callable[[LedgerDict[object, object], object, object], None] = (
        LedgerDict[object, object].__setitem__
    )
    original_note = ledger.note_store_mutation
    payload = (3, 7)
    rollback_armed = False
    rollback_callback_failed = False

    def fail_rollback_mutation() -> None:
        nonlocal rollback_armed, rollback_callback_failed
        if rollback_armed:
            rollback_armed = False
            rollback_callback_failed = True
            raise RuntimeError("injected delete callback failure")
        original_note()

    def insert_then_interrupt(
        mapping: LedgerDict[object, object], key: object, value: object
    ) -> None:
        nonlocal rollback_armed
        original_setitem(mapping, key, value)
        if mapping is store and key == "root":
            rollback_armed = True
            value = None
            raise publication_error

    monkeypatch.setattr(ledger, "note_store_mutation", fail_rollback_mutation)
    monkeypatch.setattr(LedgerDict, "__setitem__", insert_then_interrupt)
    try:
        with pytest.raises(
            KeyboardInterrupt, match="post-insert interrupt"
        ) as captured:
            memo.adopt_reserved("root", payload, reservation)

        assert captured.value is publication_error
        assert captured.value.__cause__ is None
        assert rollback_callback_failed
        assert len(memo) == 0
        assert memo.audit_snapshot().dynamic_nodes == 0
        assert ledger.account_usage(source) == (1, 3)
        assert ledger.account_usage(target) == (0, 0)
        frame = _owned_memo_write_frame(captured.value, operation="adopt_reserved")
        assert frame.f_locals["value"] is not payload
        assert frame.f_locals["stored"] is None
    finally:
        monkeypatch.undo()
        try:
            reservation.close()
        finally:
            memo.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0


@pytest.mark.parametrize("commit_transfer_before_error", (False, True))
def test_reserved_dynamic_memo_reconciles_transfer_failure_state(
    monkeypatch: pytest.MonkeyPatch,
    commit_transfer_before_error: bool,
) -> None:
    ledger = ResourceLedger()
    source = ledger.register("transfer-retry-source", "WORKSPACE")
    target = ledger.register("transfer-retry-target", "ACTION_PROGRAM")
    reservation = LedgerReservation(ledger, source)
    reservation.reserve(entries=1, nodes=3)
    memo: OwnedMemo[str, tuple[int, ...]] = OwnedMemo(
        ledger, target, node_cost=lambda _key, value: len(value)
    )
    store = memo.audit_snapshot().container
    payload = (5, 8)
    publication_error = RuntimeError("injected memo write failure")
    transfer_error = RuntimeError("injected reservation return failure")
    original_setitem: Callable[[LedgerDict[object, object], object, object], None] = (
        LedgerDict[object, object].__setitem__
    )
    original_transfer_from = ledger.transfer_reservation_from

    def insert_then_fail(
        mapping: LedgerDict[object, object], key: object, value: object
    ) -> None:
        original_setitem(mapping, key, value)
        if mapping is store and key == "root":
            value = None
            raise publication_error

    def fail_transfer_from(
        tracker: object,
        owner_id: int,
        *,
        entries: int = 0,
        nodes: int = 0,
    ) -> None:
        if tracker is reservation:
            if commit_transfer_before_error:
                original_transfer_from(tracker, owner_id, entries=entries, nodes=nodes)
            raise transfer_error
        original_transfer_from(tracker, owner_id, entries=entries, nodes=nodes)

    monkeypatch.setattr(LedgerDict, "__setitem__", insert_then_fail)
    monkeypatch.setattr(ledger, "transfer_reservation_from", fail_transfer_from)
    try:
        with pytest.raises(RuntimeError, match="memo write failure") as captured:
            memo.adopt_reserved("root", payload, reservation)

        assert captured.value is publication_error
        assert captured.value.__cause__ is transfer_error
        assert len(memo) == 0
        assert memo.audit_snapshot().dynamic_nodes == 0
        assert ledger.account_usage(target) == (0, 0)
        if commit_transfer_before_error:
            assert ledger.account_usage(source) == (1, 3)
        else:
            assert ledger.account_usage(source) == (0, 0)
    finally:
        monkeypatch.undo()
        try:
            reservation.close()
        finally:
            memo.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0
