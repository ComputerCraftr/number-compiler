"""Bounded process-local reuse for admitted immutable summaries.

The cache owns storage, accounting, and lifetime authority only.  A caller must
qualify a lease by the complete semantic source/action identity and must still
validate domain-specific admission before publishing or consuming a payload.
Complete endpoints and expanded histories are not cache payloads.
"""

from __future__ import annotations

import sys
from collections.abc import Callable, Generator
from contextlib import contextmanager
from dataclasses import dataclass
from threading import RLock
from typing import Final, Self, TypeVar, cast

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger, ResourceScope
from number_compiler.resources.lifecycle import cleanup_all

DEFAULT_PROCESS_CACHE_ENTRIES: Final = 131_072
DEFAULT_PROCESS_CACHE_BYTES: Final = 32 * 1024 * 1024
_MAX_IMMUTABLE_DEPTH: Final = 64
_ENTRY_OVERHEAD: Final = 128
# Covers one hash-table slot plus the retained pin/authority tuple and scalar
# fields.  Deep sizes below separately include all caller-supplied key material.
_LEASE_OVERHEAD: Final = 192
_UpdateMetadata = TypeVar("_UpdateMetadata")


class _Missing:
    __slots__ = ()

    def __repr__(self) -> str:
        return "MISSING"


MISSING: Final = _Missing()

ImmutableAtom = int | str | bytes | bool | None
ImmutableValue = ImmutableAtom | tuple["ImmutableValue", ...]
PartitionKey = tuple[str, str, tuple[ImmutableValue, ...]]
FullKey = tuple[PartitionKey, tuple[ImmutableValue, ...]]


@dataclass(frozen=True, slots=True)
class CacheStats:
    hits: int
    misses: int
    puts: int
    bypasses: int
    evictions: int
    entries: int
    lease_partitions: int
    bytes: int
    active_leases: int
    generation: int
    max_entries: int
    max_bytes: int
    enabled: bool


CacheRecord = tuple[PartitionKey, ImmutableValue, int, int, object | None, int]


class CacheRecordIssuerMismatch(ValueError):
    """A cache payload was not issued by the expected owner capability.

    Issuer identity records which trusted producer path published a value. It
    is not a cryptographic seal or a proof of domain-specific correctness.
    """


def _validate_immutable(
    value: object, name: str, *, allow_bool: bool = True
) -> ImmutableValue:
    """Validate the explicit cache wire domain without recursive Python calls."""
    pending = [(value, 0)]
    deepest: dict[int, int] = {}
    while pending:
        current, depth = pending.pop()
        if is_exact_object_tuple(current):
            if depth >= _MAX_IMMUTABLE_DEPTH:
                raise ValueError(f"{name} exceeds the immutable nesting limit")
            # Immutable tuples form a DAG. Revisit a shared tuple only when a
            # deeper path can strengthen the nesting check; a plain seen-set
            # would incorrectly accept over-deep aliases.
            identity = id(current)
            if deepest.get(identity, -1) >= depth:
                continue
            deepest[identity] = depth
            pending.extend((item, depth + 1) for item in current)
        elif type(current) is bool and not allow_bool:
            # bool compares and hashes like 0/1, so allowing it in an
            # authority key can cross otherwise distinct source partitions.
            raise TypeError(f"{name} cannot contain Boolean key components")
        elif current is None or type(current) in (int, str, bytes, bool):
            continue
        else:
            raise TypeError(
                f"{name} must contain only tuple/int/str/bytes/bool/None values"
            )
    # Every nested member has passed the exact immutable wire-domain check.
    return cast(ImmutableValue, value)


def _deep_size(value: object) -> int:
    """Charge an immutable wire value or an internal authority record."""
    total = 0
    pending = [value]
    seen: set[int] = set()
    while pending:
        current = pending.pop()
        identity = id(current)
        if identity in seen:
            continue
        seen.add(identity)
        total += sys.getsizeof(current)
        if is_exact_object_tuple(current):
            pending.extend(current)
    return total


class CacheLease:
    """Generation-bound authority over one source-qualified cache partition.

    The cache retains each issued lease until explicit close or reset; merely
    dropping the caller's reference does not release its pinned partition.
    """

    def __init__(
        self,
        cache: ProcessCache,
        partition: PartitionKey,
        generation: int,
        *,
        _token: int,
    ) -> None:
        self._cache = cache
        self._partition = partition
        self._generation = generation
        self._token = _token
        self._closed = False

    @property
    def source_qualification(self) -> PartitionKey:
        return self._partition

    def _require_open(self) -> None:
        if self._closed:
            raise RuntimeError("process-cache lease is closed")

    def _check_live(self) -> None:
        self._require_open()
        self._cache.validate_lease(
            id(self), self._token, self._partition, self._generation
        )

    def get(
        self,
        key: tuple[ImmutableValue, ...],
        default: object = MISSING,
    ) -> ImmutableValue | object:
        self._require_open()
        return self._cache.get_for_lease(
            self._partition,
            key,
            default,
            id(self),
            self._token,
            self._generation,
        )

    def get_issued(
        self,
        key: tuple[ImmutableValue, ...],
        issuer: object,
        default: object = MISSING,
    ) -> ImmutableValue | object:
        """Read a record published with this exact owner capability.

        Capability identity is an in-process trusted-code boundary only. It
        does not authenticate semantic correctness of the stored payload.
        """
        self._require_open()
        if type(issuer) is not object:
            raise TypeError("cache record issuer must be an exact object capability")
        return self._cache.get_for_lease(
            self._partition,
            key,
            default,
            id(self),
            self._token,
            self._generation,
            expected_issuer=issuer,
        )

    def put(
        self,
        key: tuple[ImmutableValue, ...],
        payload: ImmutableValue,
        *,
        accounted_bytes: int | None = None,
    ) -> bool:
        self._require_open()
        return self._cache.put_for_lease(
            self._partition,
            key,
            payload,
            accounted_bytes=accounted_bytes,
            lease_identity=id(self),
            token=self._token,
            generation=self._generation,
        )

    def put_issued(
        self,
        key: tuple[ImmutableValue, ...],
        payload: ImmutableValue,
        issuer: object,
        *,
        accounted_bytes: int | None = None,
    ) -> bool:
        """Publish a record with an owner capability retained by identity.

        The caller remains responsible for proving the payload's semantics.
        """
        self._require_open()
        if type(issuer) is not object:
            raise TypeError("cache record issuer must be an exact object capability")
        return self._cache.put_for_lease(
            self._partition,
            key,
            payload,
            accounted_bytes=accounted_bytes,
            lease_identity=id(self),
            token=self._token,
            generation=self._generation,
            issuer=issuer,
        )

    def update_issued(
        self,
        key: tuple[ImmutableValue, ...],
        issuer: object,
        update: Callable[[object], tuple[object, _UpdateMetadata]],
    ) -> tuple[bool | None, _UpdateMetadata | None]:
        """Atomically transform one payload owned by this exact issuer.

        The updater runs under the cache's existing lock and must be a small,
        bounded transformation returning ``(replacement, metadata)``. Returning
        ``MISSING`` as the replacement leaves the record unchanged (reported
        as ``None``); metadata is still returned for the caller to distinguish
        an already-retained value from an optional capacity miss. The updated
        immutable payload is accounted by the same path as :meth:`put_issued`.
        """
        self._require_open()
        if type(issuer) is not object:
            raise TypeError("cache record issuer must be an exact object capability")
        if not callable(update):
            raise TypeError("issued cache updater must be callable")
        return self._cache.update_issued_for_lease(
            self._partition,
            key,
            issuer,
            update,
            lease_identity=id(self),
            token=self._token,
            generation=self._generation,
        )

    def stats(self) -> CacheStats:
        self._check_live()
        return self._cache.stats()

    def close(self) -> None:
        with self._cache.lease_transaction():
            if not self._closed:
                failure = self._cache.release_lease(
                    id(self), self._token, self._partition, self._generation
                )
                self._closed = True
                if failure is not None:
                    raise failure

    def __enter__(self) -> Self:
        self._check_live()
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()


class ProcessCache:
    """Process-local bounded store of immutable, source-qualified summaries."""

    def __init__(
        self,
        *,
        max_entries: int = DEFAULT_PROCESS_CACHE_ENTRIES,
        max_bytes: int = DEFAULT_PROCESS_CACHE_BYTES,
        enabled: bool = True,
    ) -> None:
        if type(max_entries) is not int or max_entries < 1:
            raise ValueError("process-cache entry limit must be a positive integer")
        if type(max_bytes) is not int or max_bytes < 1:
            raise ValueError("process-cache byte limit must be a positive integer")
        if type(enabled) is not bool:
            raise TypeError("process-cache enabled flag must be a boolean")
        self.max_entries = max_entries
        self.max_bytes = max_bytes
        self.enabled = enabled
        self.ledger = ResourceLedger()
        entry_owner = self.ledger.register(
            "process-cache-entries", "query_memo", ResourceScope.SHARED_GLOBAL
        )
        pin_owner = self.ledger.register(
            "process-cache-leases", "spatial_binding", ResourceScope.SHARED_GLOBAL
        )
        authority_owner = self.ledger.register(
            "process-cache-authorities", "spatial_binding", ResourceScope.SHARED_GLOBAL
        )
        self._byte_owner = self.ledger.register(
            "process-cache-accounted-bytes",
            "retained_storage",
            ResourceScope.SHARED_GLOBAL,
        )
        self._entries: OwnedMemo[FullKey, CacheRecord] = OwnedMemo(
            self.ledger, entry_owner, nodes_per_entry=1, evictable=True
        )
        self._pins: OwnedMemo[PartitionKey, tuple[int, int]] = OwnedMemo(
            self.ledger, pin_owner, nodes_per_entry=1
        )
        self._authorities: OwnedMemo[
            int, tuple[int, PartitionKey, int, int, CacheLease]
        ] = OwnedMemo(self.ledger, authority_owner, nodes_per_entry=1)
        self._lock = RLock()
        self._generation = 0
        self._tick = 0
        self._token_serial = 0
        self._entry_bytes = 0
        self._lease_bytes = 0
        self._active_leases = 0
        self._reset_pending = False
        self._hits = 0
        self._misses = 0
        self._puts = 0
        self._bypasses = 0
        self._evictions = 0
        self.ledger.register_execution_root(self)

    @property
    def generation(self) -> int:
        with self._lock:
            return self._generation

    def _next_tick(self) -> int:
        self._tick += 1
        return self._tick

    @property
    def _retained_bytes(self) -> int:
        return self._entry_bytes + self._lease_bytes

    @property
    def _retained_entries(self) -> int:
        return len(self._entries) + len(self._pins) + len(self._authorities)

    def _require_live_cache(self) -> None:
        if self._reset_pending:
            raise RuntimeError("process-cache reset must finish before reuse")

    def _settle_byte_account(self) -> None:
        """Release only bytes no longer backed by entries or leases."""
        entries, charged = self.ledger.account_usage(self._byte_owner)
        retired = charged - self._retained_bytes
        if entries or retired < 0:
            raise RuntimeError("process-cache byte ownership is inconsistent")
        if retired:
            self.ledger.release(self._byte_owner, nodes=retired)

    def acquire(
        self,
        namespace: str,
        version: str,
        source_key: tuple[ImmutableValue, ...],
    ) -> CacheLease:
        if type(namespace) is not str or not namespace:
            raise ValueError("process-cache namespace must be a nonempty string")
        if type(version) is not str or not version:
            raise ValueError("process-cache version must be a nonempty string")
        source = _validate_immutable(
            source_key, "source qualification", allow_bool=False
        )
        if type(source) is not tuple:
            raise TypeError("source qualification must be a tuple")
        if not source:
            raise ValueError("source qualification must identify a source/action")
        partition: PartitionKey = (namespace, version, source)
        with self._lock:
            self._require_live_cache()
            self._settle_byte_account()
            generation = self._generation
            self._token_serial += 1
            token = self._token_serial
            pinned = self._pins.get(partition)
            partition_cost = (
                _deep_size(partition) + _LEASE_OVERHEAD if pinned is None else 0
            )
            provisional = CacheLease(self, partition, generation, _token=token)
            authority_cost = (
                _deep_size((token, id(provisional), partition, generation, provisional))
                + sys.getsizeof(vars(provisional))
                + _LEASE_OVERHEAD
            )
            extra_entries = 1 + int(pinned is None)
            if not self._make_room(
                extra_entries,
                partition_cost + authority_cost,
                excluded=None,
            ):
                raise BlockContextBudgetExceeded(
                    "process-cache capacity cannot admit a source lease"
                )
            total_cost = partition_cost + authority_cost
            try:
                self.ledger.reserve(self._byte_owner, nodes=total_cost)
                if pinned is None:
                    self._pins[partition] = (1, partition_cost)
                else:
                    count, cost = pinned
                    self._pins[partition] = (count + 1, cost)
                self._authorities[id(provisional)] = (
                    token,
                    partition,
                    generation,
                    authority_cost,
                    provisional,
                )
            except BaseException:
                try:
                    self._authorities.pop(id(provisional), None)
                    if pinned is None:
                        self._pins.pop(partition, None)
                    else:
                        self._pins[partition] = pinned
                except BaseException:
                    self._reset_pending = True
                    raise
                self._settle_byte_account()
                raise
            self._lease_bytes += total_cost
            self._active_leases += 1
            return provisional

    @contextmanager
    def lease_transaction(self) -> Generator[None]:
        """Serialize a lease lifecycle transition with cache reset and release."""
        with self._lock:
            try:
                yield
            finally:
                if not self._reset_pending:
                    self._settle_byte_account()

    def validate_lease(
        self,
        lease_identity: int,
        token: int,
        partition: PartitionKey,
        generation: int,
    ) -> None:
        with self._lock:
            self._require_live_cache()
            self._require_lease_fields(lease_identity, token, partition, generation)
            authority = self._authorities.get(lease_identity)
            if generation != self._generation:
                if authority is not None:
                    raise RuntimeError("process-cache lease has foreign authority")
                raise RuntimeError("process-cache lease is stale after reset")
            if not self._matches_authority(
                authority, lease_identity, token, partition, generation
            ):
                raise RuntimeError("process-cache lease has foreign authority")

    @staticmethod
    def _require_lease_fields(
        lease_identity: int,
        token: int,
        partition: PartitionKey,
        generation: int,
    ) -> None:
        if (
            type(lease_identity) is not int
            or type(token) is not int
            or type(partition) is not tuple
            or type(generation) is not int
        ):
            raise RuntimeError("process-cache lease has foreign authority")

    @staticmethod
    def _matches_authority(
        authority: tuple[int, PartitionKey, int, int, CacheLease] | None,
        lease_identity: int,
        token: int,
        partition: PartitionKey,
        generation: int,
    ) -> bool:
        # The issued immutable partition object is held by both the lease and
        # the authority. Value equality alone admits bool/int tuple aliases.
        return (
            authority is not None
            and type(authority[0]) is int
            and authority[0] == token
            and authority[1] is partition
            and type(authority[2]) is int
            and authority[2] == generation
            and type(authority[4]) is CacheLease
            and id(authority[4]) == lease_identity
        )

    def release_lease(
        self,
        lease_identity: int,
        token: int,
        partition: PartitionKey,
        generation: int,
    ) -> BaseException | None:
        """Retire a lease and return any error raised after its retirement."""
        with self._lock:
            self._require_live_cache()
            self._require_lease_fields(lease_identity, token, partition, generation)
            authority = self._authorities.get(lease_identity)
            if generation != self._generation:
                if authority is not None:
                    raise RuntimeError("process-cache lease has foreign authority")
                return None
            if self._active_leases < 1:
                raise RuntimeError("process-cache lease accounting underflow")
            if not self._matches_authority(
                authority, lease_identity, token, partition, generation
            ):
                raise RuntimeError("process-cache lease has foreign authority")
            assert authority is not None
            authority_cost = authority[3]
            pinned = self._pins.get(partition)
            if pinned is None:
                raise RuntimeError("process-cache source lease is not registered")
            count, cost = pinned
            failure: BaseException | None = None
            try:
                del self._authorities[lease_identity]
            except BaseException as error:
                if lease_identity in self._authorities:
                    raise
                failure = error

            target_pin = (count - 1, cost) if count > 1 else None
            try:
                if target_pin is None:
                    del self._pins[partition]
                else:
                    self._pins[partition] = target_pin
            except BaseException as error:
                if self._pins.get(partition) != target_pin:
                    # The authority is already gone. Revoke access to these
                    # partially updated stores until reset reconciles them.
                    self._reset_pending = True
                    if failure is not None:
                        raise error from failure
                    raise
                if failure is None:
                    failure = error
                else:
                    failure.add_note(f"Cache pin cleanup also failed: {error}")
            self._active_leases -= 1
            self._lease_bytes -= authority_cost + (cost if count == 1 else 0)
            return failure

    def _qualified_key(
        self, partition: PartitionKey, key: tuple[ImmutableValue, ...]
    ) -> FullKey:
        local = _validate_immutable(key, "cache key", allow_bool=False)
        if type(local) is not tuple:
            raise TypeError("cache key must be a tuple")
        return partition, local

    def _refresh_record(self, key: FullKey, record: CacheRecord) -> None:
        if record[3] == self._tick:
            return
        refreshed: CacheRecord = (
            record[0],
            record[1],
            record[2],
            self._next_tick(),
            record[4],
            record[5],
        )
        try:
            self._entries[key] = refreshed
        except BaseException:
            if self._entries.get(key) is refreshed:
                try:
                    self._entries[key] = record
                except BaseException:
                    if self._entries.get(key) is not record:
                        self._reset_pending = True
                    raise
            raise

    def get_for_lease(
        self,
        partition: PartitionKey,
        key: tuple[ImmutableValue, ...],
        default: object,
        lease_identity: int,
        token: int,
        generation: int,
        *,
        expected_issuer: object | None = None,
    ) -> ImmutableValue | object:
        with self._lock:
            self.validate_lease(lease_identity, token, partition, generation)
            full_key = self._qualified_key(partition, key)
            if not self.enabled:
                self._bypasses += 1
                return default
            record = self._entries.get(full_key)
            if record is None:
                self._misses += 1
                return default
            # An ordinary reader owns only unissued records. Issued payloads
            # belong to the producer capability that published them, even if
            # another caller accidentally reuses the same namespace/version/
            # source tuple. Without this check a cross-family reader using
            # ``get`` could bypass the isolation enforced by ``get_issued``.
            if record[4] is not expected_issuer:
                raise CacheRecordIssuerMismatch(
                    "process-cache record has another publisher capability"
                )
            self._refresh_record(full_key, record)
            self._hits += 1
            return record[1]

    def put_for_lease(
        self,
        partition: PartitionKey,
        key: tuple[ImmutableValue, ...],
        payload: ImmutableValue,
        *,
        accounted_bytes: int | None,
        lease_identity: int,
        token: int,
        generation: int,
        issuer: object | None = None,
    ) -> bool:
        with self._lock:
            self.validate_lease(lease_identity, token, partition, generation)
            full_key = self._qualified_key(partition, key)
            admitted_payload = _validate_immutable(payload, "cache payload")
            old = self._entries.get(full_key)
            if old is not None and old[4] is not issuer:
                raise CacheRecordIssuerMismatch(
                    "process-cache record has another publisher capability"
                )
            # A disabled store needs no retention estimate. Explicit accounting
            # claims still receive the same validation as enabled publications.
            if not self.enabled and accounted_bytes is None:
                self._bypasses += 1
                return False
            estimate = (
                _deep_size((full_key, admitted_payload, issuer)) + _ENTRY_OVERHEAD
            )
            if accounted_bytes is not None:
                if type(accounted_bytes) is not int or accounted_bytes < estimate:
                    raise ValueError(
                        "accounted cache bytes must cover the internal conservative estimate"
                    )
                cost = accounted_bytes
            else:
                cost = estimate
            if not self.enabled:
                self._bypasses += 1
                return False
            self._settle_byte_account()
            extra_entries = int(old is None)
            extra_bytes = cost - (0 if old is None else old[2])
            if not self._make_room(
                extra_entries, max(0, extra_bytes), excluded=full_key
            ):
                self._bypasses += 1
                return False
            tick = self._next_tick()
            record: CacheRecord = (
                partition,
                admitted_payload,
                cost,
                tick,
                issuer,
                tick,
            )
            try:
                if extra_bytes > 0:
                    self.ledger.reserve(self._byte_owner, nodes=extra_bytes)
                self._entries[full_key] = record
            except BaseException:
                if self._entries.get(full_key) is record:
                    self._entry_bytes += extra_bytes
                self._settle_byte_account()
                raise
            self._entry_bytes += extra_bytes
            self._puts += 1
            if extra_bytes < 0:
                self._settle_byte_account()
            return True

    def update_issued_for_lease(
        self,
        partition: PartitionKey,
        key: tuple[ImmutableValue, ...],
        issuer: object,
        update: Callable[[object], tuple[object, _UpdateMetadata]],
        *,
        lease_identity: int,
        token: int,
        generation: int,
    ) -> tuple[bool | None, _UpdateMetadata | None]:
        """Run one bounded issued-record read/modify/write under the cache lock."""
        with self._lock:
            self.validate_lease(lease_identity, token, partition, generation)
            full_key = self._qualified_key(partition, key)
            if not self.enabled:
                self._bypasses += 1
                return False, None
            current = self._entries.get(full_key)
            if current is not None and current[4] is not issuer:
                raise CacheRecordIssuerMismatch(
                    "process-cache record has another publisher capability"
                )
            previous: object = MISSING if current is None else current[1]
            result = update(previous)
            if type(result) is not tuple or len(result) != 2:
                raise TypeError(
                    "issued cache updater must return a replacement and metadata"
                )
            replacement, metadata = result
            # RLock permits an updater to call reset(), close its lease, or
            # publish recursively. Revalidate even on the no-op path so a
            # stale authority cannot be reported as a successful lookup.
            self.validate_lease(lease_identity, token, partition, generation)
            current_after = self._entries.get(full_key)
            if (current_after is None) != (current is None) or (
                current_after is not None
                and current is not None
                and current_after[5] != current[5]
            ):
                # A nested same-key write is already authoritative. Preserve
                # it and report this outer publication as not stored.
                return False, metadata
            if replacement is MISSING:
                if current_after is not None:
                    self._refresh_record(full_key, current_after)
                return None, metadata
            admitted_replacement = cast(ImmutableValue, replacement)
            stored = self.put_for_lease(
                partition,
                key,
                admitted_replacement,
                accounted_bytes=None,
                lease_identity=lease_identity,
                token=token,
                generation=generation,
                issuer=issuer,
            )
            return stored, metadata

    def _make_room(
        self,
        extra_entries: int,
        extra_bytes: int,
        *,
        excluded: FullKey | None,
    ) -> bool:
        if extra_entries > self.max_entries or extra_bytes > self.max_bytes:
            return False
        need_entries = self._retained_entries + extra_entries - self.max_entries
        need_bytes = self._retained_bytes + extra_bytes - self.max_bytes
        if need_entries <= 0 and need_bytes <= 0:
            return True
        candidates = [
            (record[3], key, record[2])
            for key, record in self._entries.items()
            if key != excluded and self._pins.get(record[0]) is None
        ]
        candidates.sort(key=lambda row: row[0])
        selected: list[tuple[FullKey, int]] = []
        freed_entries = freed_bytes = 0
        for _, key, cost in candidates:
            selected.append((key, cost))
            freed_entries += 1
            freed_bytes += cost
            if freed_entries >= max(0, need_entries) and freed_bytes >= max(
                0, need_bytes
            ):
                break
        if freed_entries < max(0, need_entries) or freed_bytes < max(0, need_bytes):
            return False
        for key, cost in selected:
            try:
                del self._entries[key]
            finally:
                if key not in self._entries:
                    self._entry_bytes -= cost
                    self._evictions += 1
                    self._settle_byte_account()
        return True

    def reset(self) -> None:
        """Release retained data and invalidate every previously issued lease."""
        with self._lock:
            self._reset_pending = True
            cleanup_all(
                (self._entries.clear, self._pins.clear, self._authorities.clear)
            )
            self._entry_bytes = self._lease_bytes = 0
            self._active_leases = 0
            self._generation += 1
            self._tick = 0
            self._hits = self._misses = self._puts = 0
            self._bypasses = self._evictions = 0
            self._reset_pending = False
            self._settle_byte_account()

    def stats(self) -> CacheStats:
        with self._lock:
            return CacheStats(
                hits=self._hits,
                misses=self._misses,
                puts=self._puts,
                bypasses=self._bypasses,
                evictions=self._evictions,
                entries=len(self._entries),
                lease_partitions=len(self._pins),
                bytes=self.ledger.account_usage(self._byte_owner)[1],
                active_leases=self._active_leases,
                generation=self._generation,
                max_entries=self.max_entries,
                max_bytes=self.max_bytes,
                enabled=self.enabled,
            )


_process_cache: ProcessCache | None = None
_PROCESS_CACHE_LOCK = RLock()


@contextmanager
def temporary_process_cache(
    cache: ProcessCache | None,
) -> Generator[ProcessCache | None]:
    """Temporarily install one cache and restore the previous process cache."""
    global _process_cache
    with _PROCESS_CACHE_LOCK:
        prior = _process_cache
        _process_cache = cache
    try:
        yield cache
    finally:
        with _PROCESS_CACHE_LOCK:
            _process_cache = prior


def get_process_cache() -> ProcessCache:
    """Return the lazily constructed bounded process cache."""
    global _process_cache
    with _PROCESS_CACHE_LOCK:
        if _process_cache is None:
            _process_cache = ProcessCache()
        return _process_cache


def process_cache_stats() -> CacheStats | None:
    """Read aggregate retention without creating a cache or acquiring a lease."""
    with _PROCESS_CACHE_LOCK:
        return None if _process_cache is None else _process_cache.stats()


def clear_process_cache() -> None:
    """Clear the global cache if it has been used, without constructing it."""
    with _PROCESS_CACHE_LOCK:
        if _process_cache is not None:
            _process_cache.reset()
