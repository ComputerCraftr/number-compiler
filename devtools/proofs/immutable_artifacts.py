"""Process-local registry for immutable, owner-free proof artifacts.

The registry deliberately knows nothing about runtime arenas.  Producers must
freeze their result into tuples and frozen dataclasses before publication;
consumers bind that value into a fresh scoped runtime and account for that
loading work there.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass, fields, is_dataclass
from sys import getsizeof
from threading import RLock
from typing import TypeVar, cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken

_SCHEMA_VERSION = "proof-artifact-v1"
T = TypeVar("T")


@dataclass(frozen=True, slots=True)
class ArtifactKey:
    kind: str
    recipe_digest: str
    schema_version: str = _SCHEMA_VERSION

    def __post_init__(self) -> None:
        if (
            type(self.kind) is not str
            or not self.kind
            or type(self.recipe_digest) is not str
            or not self.recipe_digest
            or type(self.schema_version) is not str
            or self.schema_version != _SCHEMA_VERSION
        ):
            raise ValueError(
                "proof artifacts require a kind, digest, and current schema"
            )


@dataclass(frozen=True, slots=True)
class UncachedBuild:
    requester: str
    reason: str

    def __post_init__(self) -> None:
        if (
            type(self.requester) is not str
            or not self.requester
            or type(self.reason) is not str
            or not self.reason
        ):
            raise ValueError("uncached proof builds require requester and reason")


@dataclass(frozen=True, slots=True)
class ArtifactStats:
    builds: int
    hits: int
    uncached_builds: int
    retained_bytes: int
    uncached_requests: tuple[UncachedBuild, ...]
    failed_builds: int


def _immutable(value: object) -> bool:
    """Admit recursively immutable data without walking through live objects."""
    pending = [(value, False)]
    active: set[int] = set()
    complete: set[int] = set()
    while pending:
        item, leaving = pending.pop()
        identity = id(item)
        if leaving:
            active.remove(identity)
            complete.add(identity)
            continue
        if identity in complete:
            continue
        if identity in active:
            return False
        if item is None or type(item) in (bool, int, str, bytes):
            complete.add(identity)
            continue
        if isinstance(item, (ArenaHandle, ArenaToken)):
            return False
        active.add(identity)
        pending.append((item, True))
        if type(item) is tuple:
            pending.extend((child, False) for child in item)
            continue
        if (
            is_dataclass(item)
            and getattr(type(item), "__dataclass_params__").frozen
            and not hasattr(item, "__dict__")
        ):
            declared_fields = {field.name for field in fields(item)}
            storage_slots: set[str] = set()
            for cls in cast(tuple[type, ...], type(item).__mro__):
                raw_slots = cls.__dict__.get("__slots__", ())
                if type(raw_slots) is str:
                    slots: tuple[object, ...] = (raw_slots,)
                elif type(raw_slots) is tuple:
                    slots = cast(tuple[object, ...], raw_slots)
                else:
                    return False
                for slot in slots:
                    if type(slot) is not str:
                        return False
                    if slot not in ("__dict__", "__weakref__"):
                        storage_slots.add(slot)
            if not storage_slots <= declared_fields:
                return False
            pending.extend((getattr(item, field.name), False) for field in fields(item))
            continue
        return False
    return True


def _retained_bytes(value: object) -> int:
    """Deterministic payload estimate; it never invokes user callbacks."""
    total = 0
    pending = [value]
    seen: set[int] = set()
    while pending:
        item = pending.pop()
        identity = id(item)
        if identity in seen:
            continue
        seen.add(identity)
        total += getsizeof(item)
        if type(item) is tuple:
            pending.extend(item)
        elif is_dataclass(item):
            pending.extend(getattr(item, field.name) for field in fields(item))
    return total


class ImmutableArtifactRegistry:
    """Small proof-only registry; artifacts never contain scoped runtime IDs."""

    def __init__(self) -> None:
        self._lock = RLock()
        self._artifacts: dict[ArtifactKey, object] = {}
        self._builds: dict[str, int] = {}
        self._hits: dict[str, int] = {}
        self._uncached: dict[str, int] = {}
        self._uncached_requests: dict[str, list[UncachedBuild]] = {}
        self._failed: dict[str, int] = {}
        self._bytes: dict[str, int] = {}

    def obtain(
        self,
        key: ArtifactKey,
        builder: Callable[[], T],
        *,
        uncached: UncachedBuild | None = None,
    ) -> tuple[T, bool]:
        if type(key) is not ArtifactKey or not callable(builder):
            raise TypeError("invalid proof artifact request")
        key.__post_init__()
        if uncached is not None and type(uncached) is not UncachedBuild:
            raise TypeError("invalid uncached proof build request")
        if uncached is not None:
            uncached.__post_init__()
        with self._lock:
            if uncached is None:
                sentinel = object()
                found = self._artifacts.get(key, sentinel)
                if found is not sentinel:
                    self._hits[key.kind] = self._hits.get(key.kind, 0) + 1
                    return cast(T, found), True
            try:
                value = builder()
                if not _immutable(value):
                    raise TypeError(
                        "proof artifacts must contain only immutable owner-free data"
                    )
            except BaseException:
                self._failed[key.kind] = self._failed.get(key.kind, 0) + 1
                raise
            self._builds[key.kind] = self._builds.get(key.kind, 0) + 1
            if uncached is not None:
                self._uncached[key.kind] = self._uncached.get(key.kind, 0) + 1
                self._uncached_requests.setdefault(key.kind, []).append(uncached)
                return value, False
            existing = self._artifacts.get(key)
            if existing is not None:
                self._hits[key.kind] = self._hits.get(key.kind, 0) + 1
                return cast(T, existing), True
            self._artifacts[key] = value
            self._bytes[key.kind] = self._bytes.get(key.kind, 0) + _retained_bytes(
                value
            )
            return value, False

    def stats(self) -> Mapping[str, ArtifactStats]:
        with self._lock:
            kinds = (
                self._builds.keys()
                | self._hits.keys()
                | self._bytes.keys()
                | self._failed.keys()
                | self._uncached.keys()
            )
            return {
                kind: ArtifactStats(
                    self._builds.get(kind, 0),
                    self._hits.get(kind, 0),
                    self._uncached.get(kind, 0),
                    self._bytes.get(kind, 0),
                    tuple(self._uncached_requests.get(kind, ())),
                    self._failed.get(kind, 0),
                )
                for kind in kinds
            }


REGISTRY = ImmutableArtifactRegistry()


__all__ = [
    "ArtifactKey",
    "ArtifactStats",
    "ImmutableArtifactRegistry",
    "REGISTRY",
    "UncachedBuild",
]
