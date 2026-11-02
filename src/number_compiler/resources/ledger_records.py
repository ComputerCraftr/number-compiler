"""Ledger account state and immutable records shared by resource reports."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Sized
from dataclasses import dataclass, field
from enum import StrEnum

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle


class ResourceScope(StrEnum):
    ENGINE_OWNED = "ENGINE_OWNED"
    INDEX_OWNED = "INDEX_OWNED"
    SHARED_GLOBAL = "SHARED_GLOBAL"


def _empty_root_map() -> dict[ArenaHandle, None]:
    return {}


@dataclass(slots=True)
class LedgerAccount:
    name: str
    role: str
    scope: ResourceScope
    entries: int = 0
    nodes: int = 0
    roots: dict[ArenaHandle, None] = field(default_factory=_empty_root_map)
    container: Sized | None = None
    node_count: Callable[[], int] | None = None
    payloads: Callable[[], Iterable[object]] | None = None
    root_resolver: Callable[[], Iterable[object]] | None = None
    evict: Callable[[], None] | None = None
    composition_count: Callable[[], int] | None = None
    disposed: bool = False


@dataclass(frozen=True, slots=True)
class ResourceInventory:
    owner: int
    name: str
    role: str
    scope: ResourceScope
    entries: int
    nodes: int
    roots: tuple[ArenaHandle, ...]
    observed_entries: int | None = None
    observed_nodes: int | None = None
    payloads_registered: bool = False
    evictable: bool = False
    composition_entries: int = 0
    disposed: bool = False

    @property
    def accounting_delta(self) -> int | None:
        if self.observed_entries is None:
            return None
        return abs(self.observed_entries - self.entries) + (
            0 if self.observed_nodes is None else abs(self.observed_nodes - self.nodes)
        )


@dataclass(frozen=True, slots=True)
class LedgerSnapshot:
    entries: int
    nodes: int
    peak_entries: int
    peak_nodes: int
    counters: dict[str, int]
    inventory: tuple[ResourceInventory, ...]


@dataclass(frozen=True, slots=True)
class LedgerAccountStatus:
    """Reservation state without invoking payload or root resolvers."""

    role: str
    entries: int
    nodes: int
    disposed: bool
    container_identity: int | None
