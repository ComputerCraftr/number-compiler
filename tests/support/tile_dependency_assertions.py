"""Shared snapshots for causal dependency and tile-lease failure tests."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.tile_dependency_leases import TileDependencyLeases


@dataclass(frozen=True, slots=True)
class TileDependencySnapshot:
    records: tuple[tuple[tuple[int, TileID], TileLease], ...]
    dependency_entries: int
    tile_lease_entries: int
    tile_references: tuple[tuple[int, int], ...] | None
    tile_leases: tuple[tuple[int, TileID], ...] | None
    counters: tuple[tuple[str, int], ...] | None


def capture_tile_dependency_state(
    ledger: ResourceLedger,
    tiles: TileArena,
    dependencies: TileDependencyLeases,
    *,
    include_tile_state: bool = False,
    include_counters: bool = False,
) -> TileDependencySnapshot:
    inventory = ledger.inventory()
    tile_state = tiles.audit_snapshot()
    return TileDependencySnapshot(
        tuple(dependencies.records.items()),
        inventory[dependencies.owner].entries,
        inventory[tile_state.lease_owner].entries,
        tuple(tile_state.refs.items()) if include_tile_state else None,
        tuple(tile_state.leases.items()) if include_tile_state else None,
        tuple(ledger.counters.items()) if include_counters else None,
    )


def assert_tile_dependency_state(
    expected: TileDependencySnapshot,
    ledger: ResourceLedger,
    tiles: TileArena,
    dependencies: TileDependencyLeases,
) -> None:
    actual = capture_tile_dependency_state(
        ledger,
        tiles,
        dependencies,
        include_tile_state=expected.tile_references is not None,
        include_counters=expected.counters is not None,
    )
    assert actual == expected
