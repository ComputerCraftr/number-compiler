"""Abort newly owned, unissued runtime arenas after a failed factory call."""

from __future__ import annotations

from types import TracebackType
from typing import Self

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


class RuntimeConstruction:
    """Construction scope for private arenas that have not escaped their factory.

    Existing owners and canonical nodes are never rewound. Aborted owner IDs
    remain disposed, so neither owner identities nor their handles are recycled.
    This scope is not a transaction for mutations of an already issued arena.
    """

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("runtime construction requires an index ledger")
        self.ledger = ledger
        self._first_owner = len(ledger._accounts)
        self._roots = frozenset(ledger._execution_roots)
        self._entered = False

    def __enter__(self) -> Self:
        if self._entered:
            raise RuntimeError("runtime construction cannot be entered twice")
        self._entered = True
        return self

    def __exit__(
        self,
        kind: type[BaseException] | None,
        exception: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        if kind is None:
            return
        ledger = self.ledger
        retired_entries = retired_nodes = 0
        for owner in range(len(ledger._accounts) - 1, self._first_owner - 1, -1):
            account = ledger._accounts[owner]
            if account.disposed:
                continue
            retired_entries += account.entries
            retired_nodes += account.nodes
            if isinstance(account.container, (LedgerDict, LedgerList)):
                # These unpublished stores have no valid external handles.
                # Clear backing storage before retiring their owner, including
                # append-only identity arrays; the owner ID is never reused.
                account.container._data.clear()
            ledger.release(owner, account.entries, account.nodes)
            if account.container is not None:
                ledger._factory_containers.discard(id(account.container))
            # Drop the ledger's owning references, including bound callbacks.
            # Factory frames may remain in an exception traceback temporarily;
            # they are not issued execution roots or live index-owned arenas.
            account.container = None
            account.node_count = account.payloads = account.root_resolver = None
            account.evict = account.composition_count = None
            account.roots.clear()
            ledger.mark_disposed(owner)
        for identity in tuple(ledger._execution_roots):
            if identity not in self._roots:
                del ledger._execution_roots[identity]
        ledger.bump("runtime_construction_aborts")
        ledger.bump("runtime_construction_released_entries", retired_entries)
        ledger.bump("runtime_construction_released_nodes", retired_nodes)
        ledger.note_store_mutation()


__all__ = ["RuntimeConstruction"]
