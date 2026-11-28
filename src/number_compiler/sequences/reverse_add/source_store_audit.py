"""Authority audit for retained reverse source-image workspaces."""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from typing import Protocol, TypeVar, cast

from number_compiler.resources.ledger import (
    OwnedMemo,
    ResourceInventory,
    ResourceLedger,
)
from number_compiler.resources.owned_memo import (
    DynamicMemoValue,
    OwnedMemoAuditSnapshot,
)
from number_compiler.resources.stores import LedgerDict, LedgerList

_AuditKey = TypeVar("_AuditKey")
_AuditValue = TypeVar("_AuditValue")


class _LedgerSizedStore(Protocol):
    owner: int
    ledger: ResourceLedger
    nodes_per_entry: int

    def __len__(self) -> int: ...


def audit_payload_items(
    snapshot: OwnedMemoAuditSnapshot[_AuditKey, _AuditValue],
) -> Iterator[tuple[_AuditKey, object]]:
    """Read current memo payloads while preserving malformed-wrapper evidence."""
    view = snapshot.payload_view
    for key in snapshot.container:
        try:
            yield key, view[key]
        except TypeError:
            # Keep malformed dynamic entries visible to exact payload checks.
            yield key, snapshot.container[key]


def audit_payload_value(
    snapshot: OwnedMemoAuditSnapshot[_AuditKey, _AuditValue], key: _AuditKey
) -> object:
    if key not in snapshot.container:
        return _MISSING
    try:
        return snapshot.payload_view[key]
    except TypeError:
        return snapshot.container[key]


_MISSING = object()


def store_valid_for_audit(
    ledger: ResourceLedger,
    owner: object,
    store: object,
    expected_role: str,
    containers: Mapping[int, object],
    inventory: Mapping[int, object],
) -> bool:
    if type(ledger) is not ResourceLedger or type(owner) is not int:
        return False
    item = inventory.get(owner)
    if type(item) is not ResourceInventory:
        return False
    owned_container: object | None = None
    entries = 0
    expected_nodes = 0
    if type(store) is OwnedMemo:
        snapshot = cast(OwnedMemo[object, object], store).audit_snapshot()
    elif type(store) is OwnedMemoAuditSnapshot:
        snapshot = cast(OwnedMemoAuditSnapshot[object, object], store)
    else:
        snapshot = None
    if snapshot is not None:
        data: Mapping[object, object] = snapshot.container
        if (
            snapshot.ledger is not ledger
            or snapshot.owner != owner
            or snapshot.disposed
        ):
            return False
        owned_container = data
        entries = len(data)
        if not snapshot.dynamic_cost:
            expected_nodes = entries * snapshot.nodes_per_entry
        else:
            expected_nodes = snapshot.dynamic_nodes
            measured_nodes = 0
            for raw_value in data.values():
                value: object = raw_value
                if type(value) is not DynamicMemoValue:
                    return False
                if type(value.nodes) is not int or value.nodes < 1:
                    return False
                measured_nodes += value.nodes
            if measured_nodes != expected_nodes:
                return False
    elif isinstance(store, (LedgerList, LedgerDict)):
        owned_store = cast(_LedgerSizedStore, store)
        owned_container = cast(object, store)
        entries = len(owned_store)
        expected_nodes = entries * owned_store.nodes_per_entry
        if owned_store.owner != owner or owned_store.ledger is not ledger:
            return False
    else:
        return False
    try:
        registered_container = ledger.registered_container(owner)
    except (IndexError, RuntimeError, TypeError, ValueError):
        return False
    return (
        containers.get(owner) is owned_container
        and registered_container is owned_container
        and not item.disposed
        and item.payloads_registered
        and item.role == expected_role
        and item.entries == entries
        and item.nodes == expected_nodes
    )
