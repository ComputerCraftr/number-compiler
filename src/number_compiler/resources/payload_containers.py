"""Read actual factory entries without rehashing adversarial mutated keys."""

from __future__ import annotations

from collections.abc import Mapping
from gc import get_referents
from types import MappingProxyType
from typing import TypeVar, cast

from number_compiler.resources.owned_memo import DynamicMemoValue, OwnedMemo
from number_compiler.resources.stores import LedgerDict

_K = TypeVar("_K")
_V = TypeVar("_V")


def audit_mapping_items(value: Mapping[_K, _V]) -> tuple[tuple[_K, _V], ...]:
    """Bypass lookup only for the exact, still-registered ledger factory store."""
    current: Mapping[object, object] = cast(Mapping[object, object], value)
    visited: set[int] = set()
    while isinstance(current, MappingProxyType):
        if id(current) in visited:
            raise ValueError("cyclic mapping facade")
        visited.add(id(current))
        backing = get_referents(current)
        if len(backing) != 1 or not isinstance(backing[0], Mapping):
            break
        current = cast(Mapping[object, object], backing[0])
    if type(current) is OwnedMemo:
        memo = cast(OwnedMemo[object, object], current)
        snapshot = memo.audit_snapshot()
        store = snapshot.container
        if type(store) is LedgerDict:
            ledger_store = cast(LedgerDict[object, object], store)
            if (
                ledger_store.ledger is snapshot.ledger
                and ledger_store.owner == snapshot.owner
                and ledger_store.ledger.is_factory_container(ledger_store)
                and any(
                    owner == ledger_store.owner and container is ledger_store
                    for owner, container in ledger_store.ledger.iter_containers()
                )
            ):
                rows = tuple(ledger_store.items())
                if snapshot.dynamic_cost:
                    payload_rows: list[tuple[object, object]] = []
                    for key, stored in rows:
                        if not isinstance(stored, DynamicMemoValue):
                            raise TypeError(
                                "dynamic memo entry has invalid cost metadata"
                            )
                        dynamic = cast(DynamicMemoValue[object], stored)
                        payload_rows.append((key, dynamic.value))
                    rows = tuple(payload_rows)
                return cast(tuple[tuple[_K, _V], ...], rows)
    current_object = cast(object, current)
    if type(current_object) is LedgerDict:
        ledger_store = cast(LedgerDict[object, object], current_object)
        if ledger_store.ledger.is_factory_container(ledger_store) and any(
            owner == ledger_store.owner and container is ledger_store
            for owner, container in ledger_store.ledger.iter_containers()
        ):
            return cast(tuple[tuple[_K, _V], ...], tuple(ledger_store.items()))
    try:
        fallback_mapping = cast(Mapping[object, object], current)
        return cast(tuple[tuple[_K, _V], ...], tuple(fallback_mapping.items()))
    except (KeyError, TypeError):
        # Read-only mapping facades may delegate iteration through key lookup.
        # A maliciously mutated frozen key then becomes unhashable even though
        # the registered backing store can still be inspected safely.
        for backing in get_referents(current):
            if type(backing) is LedgerDict:
                store = cast(LedgerDict[object, object], backing)
                if store.ledger.is_factory_container(store):
                    return cast(tuple[tuple[_K, _V], ...], tuple(store.items()))
        raise
