"""Read actual factory entries without rehashing adversarial mutated keys."""

from __future__ import annotations

from collections.abc import Mapping
from gc import get_referents
from types import MappingProxyType
from typing import TypeVar, cast

from number_compiler.resources.stores import LedgerDict

_K = TypeVar("_K")
_V = TypeVar("_V")


def audit_mapping_items(value: Mapping[_K, _V]) -> tuple[tuple[_K, _V], ...]:
    """Bypass lookup only for the exact, still-registered ledger factory store."""
    from number_compiler.resources.ledger import OwnedMemo

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
        store = current._data
        if (
            type(store) is LedgerDict
            and store.ledger is current.ledger
            and store.owner == current.owner
            and store.ledger.is_factory_container(store)
            and any(
                owner == store.owner and container is store
                for owner, container in store.ledger.iter_containers()
            )
        ):
            return cast(tuple[tuple[_K, _V], ...], tuple(store._data.items()))
    if (
        type(current) is LedgerDict
        and current.ledger.is_factory_container(current)
        and any(
            owner == current.owner and container is current
            for owner, container in current.ledger.iter_containers()
        )
    ):
        return cast(tuple[tuple[_K, _V], ...], tuple(current._data.items()))
    try:
        return cast(tuple[tuple[_K, _V], ...], tuple(current.items()))
    except (KeyError, TypeError):
        # Read-only mapping facades may delegate iteration through key lookup.
        # A maliciously mutated frozen key then becomes unhashable even though
        # the registered backing store can still be inspected safely.
        for backing in get_referents(current):
            if type(backing) is LedgerDict and backing.ledger.is_factory_container(
                backing
            ):
                return tuple(backing._data.items())
        raise
