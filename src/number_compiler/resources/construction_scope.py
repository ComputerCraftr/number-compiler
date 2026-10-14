"""Abort newly owned, unissued runtime arenas after a failed factory call."""

from __future__ import annotations

from contextvars import ContextVar, Token
from functools import partial
from types import TracebackType
from typing import Self
from weakref import ReferenceType

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.stores import LedgerDict, LedgerList

_ACTIVE_CONSTRUCTIONS: ContextVar[tuple[RuntimeConstruction, ...]] = ContextVar(
    "active_runtime_constructions", default=()
)


def record_construction_owner(ledger: ResourceLedger, owner: int) -> None:
    """Attach a newly registered owner to each active scope for its ledger."""
    scopes = tuple(
        scope for scope in _ACTIVE_CONSTRUCTIONS.get() if scope.ledger is ledger
    )
    try:
        for scope in scopes:
            scope._record_owner(owner)
    except BaseException:
        for scope in scopes:
            scope._discard_owner(owner)
        raise


def forget_construction_owner(ledger: ResourceLedger, owner: int) -> None:
    """Undo scope bookkeeping when the ledger registration itself fails."""
    for scope in _ACTIVE_CONSTRUCTIONS.get():
        if scope.ledger is ledger:
            scope._discard_owner(owner)


def record_construction_root(
    ledger: ResourceLedger,
    identity: int,
    reference: ReferenceType[object],
) -> None:
    """Attach a newly registered execution root to its active ledger scopes."""
    scopes = tuple(
        scope for scope in _ACTIVE_CONSTRUCTIONS.get() if scope.ledger is ledger
    )
    try:
        for scope in scopes:
            scope._record_root(identity, reference)
    except BaseException:
        for scope in scopes:
            scope._discard_root(identity, reference)
        raise


def forget_construction_root(
    ledger: ResourceLedger,
    identity: int,
    reference: ReferenceType[object],
) -> None:
    """Undo root bookkeeping when weak-root registration itself fails."""
    for scope in _ACTIVE_CONSTRUCTIONS.get():
        if scope.ledger is ledger:
            scope._discard_root(identity, reference)


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
        self._owners: list[int] = []
        self._roots: dict[int, ReferenceType[object]] = {}
        self._entered = False
        self._token: Token[tuple[RuntimeConstruction, ...]] | None = None

    def __enter__(self) -> Self:
        if self._entered:
            raise RuntimeError("runtime construction cannot be entered twice")
        self._entered = True
        self._token = _ACTIVE_CONSTRUCTIONS.set((*_ACTIVE_CONSTRUCTIONS.get(), self))
        return self

    def _record_owner(self, owner: int) -> None:
        self._owners.append(owner)

    def _discard_owner(self, owner: int) -> None:
        try:
            self._owners.remove(owner)
        except ValueError:
            pass

    def _record_root(self, identity: int, reference: ReferenceType[object]) -> None:
        self._roots[identity] = reference

    def _discard_root(self, identity: int, reference: ReferenceType[object]) -> None:
        if self._roots.get(identity) is reference:
            del self._roots[identity]

    def __exit__(
        self,
        kind: type[BaseException] | None,
        exception: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        token = self._token
        if token is None:
            raise RuntimeError("runtime construction exited before entry")
        active = _ACTIVE_CONSTRUCTIONS.get()
        if not active or active[-1] is not self:
            raise RuntimeError("runtime construction scopes must exit in LIFO order")
        # Reset first: a copied Context inherits the active-scope value, but
        # cannot consume this context's Token. Validate that ownership before
        # disposing any resources.
        _ACTIVE_CONSTRUCTIONS.reset(token)
        self._token = None
        if kind is not None:
            self._abort()

    def _abort(self) -> None:
        ledger = self.ledger
        ledger.bump("runtime_construction_aborts")
        try:
            cleanup_all(
                (
                    *(
                        partial(self._retire_owner, owner)
                        for owner in reversed(self._owners)
                    ),
                    *(
                        partial(ledger._expire_execution_root, identity, reference)
                        for identity, reference in self._roots.items()
                    ),
                )
            )
        finally:
            ledger.note_store_mutation()

    def _retire_owner(self, owner: int) -> None:
        ledger = self.ledger
        account = ledger._account(owner)
        if account.disposed:
            return
        entries, nodes = account.entries, account.nodes
        if isinstance(account.container, (LedgerDict, LedgerList)):
            # These unpublished stores have no valid external handles. Owner
            # IDs are never recycled, including after a partial rollback.
            account.container._data.clear()
        ledger.release(owner, entries, nodes)
        ledger.bump("runtime_construction_released_entries", entries)
        ledger.bump("runtime_construction_released_nodes", nodes)
        if account.container is not None:
            ledger._factory_containers.discard(id(account.container))
        # Drop owning references and callbacks retained by failed factory frames.
        account.container = None
        account.node_count = account.payloads = account.root_resolver = None
        account.evict = account.composition_count = None
        account.roots.clear()
        ledger.mark_disposed(owner)


__all__ = ["RuntimeConstruction"]
