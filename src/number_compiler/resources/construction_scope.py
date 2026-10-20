"""Abort newly owned, unissued runtime arenas after a failed factory call."""

from __future__ import annotations

from contextvars import ContextVar, Token
from functools import partial
from types import TracebackType
from typing import Self
from weakref import ReferenceType

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import resources as _resources_keys

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
            scope.record_owner(owner)
    except BaseException:
        for scope in scopes:
            scope.discard_owner(owner)
        raise


def forget_construction_owner(ledger: ResourceLedger, owner: int) -> None:
    """Undo scope bookkeeping when the ledger registration itself fails."""
    for scope in _ACTIVE_CONSTRUCTIONS.get():
        if scope.ledger is ledger:
            scope.discard_owner(owner)


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
            scope.record_root(identity, reference)
    except BaseException:
        for scope in scopes:
            scope.discard_root(identity, reference)
        raise


def forget_construction_root(
    ledger: ResourceLedger,
    identity: int,
    reference: ReferenceType[object],
) -> None:
    """Undo root bookkeeping when weak-root registration itself fails."""
    for scope in _ACTIVE_CONSTRUCTIONS.get():
        if scope.ledger is ledger:
            scope.discard_root(identity, reference)


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

    def record_owner(self, owner: int) -> None:
        self._owners.append(owner)

    def discard_owner(self, owner: int) -> None:
        try:
            self._owners.remove(owner)
        except ValueError:
            pass

    def record_root(self, identity: int, reference: ReferenceType[object]) -> None:
        self._roots[identity] = reference

    def discard_root(self, identity: int, reference: ReferenceType[object]) -> None:
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
        ledger.bump(_resources_keys.RUNTIME_CONSTRUCTION_ABORTS)
        try:
            cleanup_all(
                (
                    *(
                        partial(ledger.retire_unpublished_owner, owner)
                        for owner in reversed(self._owners)
                    ),
                    *(
                        partial(ledger.expire_execution_root, identity, reference)
                        for identity, reference in self._roots.items()
                    ),
                )
            )
        finally:
            ledger.note_store_mutation()


__all__ = ["RuntimeConstruction"]
