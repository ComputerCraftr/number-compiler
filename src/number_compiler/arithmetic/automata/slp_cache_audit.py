"""Read-only forensic views for SLP projector cache ownership."""

from __future__ import annotations

from collections.abc import Iterator, Mapping, MutableMapping
from types import MappingProxyType
from typing import TYPE_CHECKING, Generic, TypeVar, cast

if TYPE_CHECKING:
    from number_compiler.resources.owned_memo import (
        OwnedMemoAuditSnapshot,
    )

_CacheKey = TypeVar("_CacheKey")
_CacheValue = TypeVar("_CacheValue")


class SLPCacheAuditView(Mapping[_CacheKey, object], Generic[_CacheKey]):
    """Read-only projector cache view with its exact backing identity."""

    __slots__ = ("_values", "_backing_store_identity", "_owner_snapshot")

    def __init__(
        self,
        values: Mapping[_CacheKey, object],
        backing_store_identity: object,
        owner_snapshot: OwnedMemoAuditSnapshot[object, object] | None = None,
    ) -> None:
        self._values = values
        self._backing_store_identity = backing_store_identity
        self._owner_snapshot = owner_snapshot

    def __getitem__(self, key: _CacheKey) -> object:
        return self._values[key]

    def __iter__(self) -> Iterator[_CacheKey]:
        return iter(self._values)

    def __len__(self) -> int:
        return len(self._values)

    @property
    def backing_store_identity(self) -> object:
        """Expose backing identity without exposing mutation operations."""
        return self._backing_store_identity

    @property
    def owner_snapshot(self) -> OwnedMemoAuditSnapshot[object, object] | None:
        """Expose exact resource ownership and immutable consumer-claim state."""
        return self._owner_snapshot


def slp_cache_audit_view(
    store: MutableMapping[_CacheKey, _CacheValue],
) -> SLPCacheAuditView[_CacheKey]:
    """Expose one mapping read-only with backing and ledger provenance."""
    from number_compiler.resources.owned_memo import OwnedMemo

    values: Mapping[_CacheKey, object]
    if type(store) is OwnedMemo:
        memo = cast(OwnedMemo[_CacheKey, _CacheValue], store)
        snapshot: OwnedMemoAuditSnapshot[_CacheKey, _CacheValue] = memo.audit_snapshot()
        payload_view = snapshot.payload_view
        values = payload_view
        backing_store = payload_view.backing_store_identity
        audit_snapshot = cast("OwnedMemoAuditSnapshot[object, object]", snapshot)
        return SLPCacheAuditView(values, backing_store, audit_snapshot)
    values = MappingProxyType(store)
    return SLPCacheAuditView(values, store)
