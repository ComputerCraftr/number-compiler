"""Immutable inventory records shared by resource owners and reports."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle


class ResourceScope(StrEnum):
    ENGINE_OWNED = "ENGINE_OWNED"
    INDEX_OWNED = "INDEX_OWNED"
    SHARED_GLOBAL = "SHARED_GLOBAL"


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
