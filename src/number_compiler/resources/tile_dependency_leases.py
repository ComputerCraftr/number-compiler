"""Application-owned exact inputs retained for causal result reuse."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_application_authority import (
        TileApplicationRegistry,
    )


@dataclass(frozen=True, slots=True)
class DependencyLeaseBatch:
    """New dependency bindings published by one atomic pin attempt."""

    bindings: tuple[tuple[int, TileID], ...]


class TileDependencyLeases:
    """Charged per-application roots for transient causal request inputs."""

    def __init__(
        self,
        ledger: ResourceLedger,
        tiles: TileArena,
        prefix: str,
        applications: TileApplicationRegistry,
    ) -> None:
        if type(ledger) is not ResourceLedger or type(tiles) is not TileArena:
            raise TypeError("causal dependency leases require one tile ledger")
        if tiles.ledger is not ledger:
            raise ValueError("causal dependency tiles belong to another index")
        from number_compiler.hashlife.execution.tile_application_authority import (
            TileApplicationRegistry,
        )

        if (
            type(applications) is not TileApplicationRegistry
            or applications.ledger is not ledger
        ):
            raise ValueError("causal dependencies require scheduler applications")
        self.ledger, self.tiles, self.applications = ledger, tiles, applications
        self.owner = ledger.register(
            prefix + "-causal-inputs",
            "tile_application_causal_input_pin",
        )
        self.records: LedgerDict[tuple[int, TileID], TileLease] = ledger.make_dict(
            self.owner,
        )
        ledger.register_container(
            self.owner,
            self.records,
            payloads=self.records.items,
            node_count=lambda: 0,
        )

    def acquire(
        self,
        application: int,
        tile_ids: tuple[TileID, ...],
    ) -> DependencyLeaseBatch:
        """Publish missing distinct roots, rolling back every partial write."""
        if type(application) is not int or application < 0:
            raise ValueError("causal dependency requires an exact application identity")
        if type(tile_ids) is not tuple or any(
            type(tile) is not TileID for tile in tile_ids
        ):
            raise TypeError("causal dependencies require exact tile IDs")
        unique = tuple(dict.fromkeys(tile_ids))
        for tile in unique:
            self.tiles.resolve(tile)
        missing: list[tuple[int, TileID]] = []
        for tile in unique:
            binding = application, tile
            found = self.records.get(binding)
            if found is None:
                missing.append(binding)
            elif type(found) is not TileLease or found.tile != tile:
                raise ValueError("causal dependency binding is corrupt")
        bindings = tuple(missing)
        reservations = (
            (self.owner, len(bindings), 0),
            (self.tiles._lease_owner, len(bindings), 0),
        )
        self.ledger.reserve_many(reservations)
        leases: list[TileLease] = []
        try:
            for _, tile in bindings:
                leases.append(self.tiles._acquire_reserved(tile))
            for binding, lease in zip(bindings, leases, strict=True):
                self.records[binding] = lease
        except BaseException:
            for binding in bindings:
                self.records.pop(binding, None)
            for lease in reversed(leases):
                lease.close()
            self.ledger.release(
                self.tiles._lease_owner,
                entries=len(bindings) - len(leases),
            )
            self.ledger.release(self.owner, entries=len(bindings))
            raise
        return DependencyLeaseBatch(bindings)

    def rollback(self, batch: DependencyLeaseBatch) -> None:
        """Remove precisely the roots introduced by a failed result pin."""
        if type(batch) is not DependencyLeaseBatch:
            raise TypeError("causal dependency rollback requires its issued batch")
        leases: list[TileLease] = []
        for binding in batch.bindings:
            lease = self.records.pop(binding, None)
            if type(lease) is not TileLease or lease.tile != binding[1]:
                raise ValueError("causal dependency rollback lost a binding")
            leases.append(lease)
        for lease in reversed(leases):
            lease.close()
        self.ledger.release(self.owner, entries=len(batch.bindings))

    def release_application(self, application: int) -> None:
        """Release all exact causal inputs owned by one application."""
        if type(application) is not int or application < 0:
            raise ValueError(
                "causal dependency release requires an application identity"
            )
        bindings = tuple(key for key in self.records if key[0] == application)
        for binding in reversed(bindings):
            lease = self.records[binding]
            try:
                self.records.pop(binding)
            except BaseException:
                if binding not in self.records:
                    self.records[binding] = lease
                raise
            try:
                lease.close()
            except BaseException:
                if not lease._closed:
                    self.records[binding] = lease
                else:
                    self.ledger.release(self.owner, entries=1)
                raise
            self.ledger.release(self.owner, entries=1)


def audit_tile_dependency_leases(
    dependencies: TileDependencyLeases,
    containers: Mapping[int, object],
) -> tuple[set[int], set[tuple[int, int]]]:
    """Independently reconcile dependency roots with their charged store."""
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    inventory = {item.owner: item for item in dependencies.ledger.inventory()}
    account = inventory.get(dependencies.owner)
    valid_store = (
        containers.get(dependencies.owner) is dependencies.records
        and account is not None
        and account.entries == len(dependencies.records)
        and account.observed_entries == len(dependencies.records)
    )
    for binding, lease in dependencies.records.items():
        valid = (
            type(binding) is tuple and len(binding) == 2 and type(lease) is TileLease
        )
        try:
            application, tile = binding
            valid &= (
                type(application) is int
                and application >= 0
                and type(tile) is TileID
                and lease.tile == tile
                and dependencies.tiles.resolve(tile) is not None
            )
        except (TypeError, ValueError, KeyError, AttributeError, IndexError):
            valid = False
        if valid:
            approved.update((id(binding), id(lease)))
        else:
            invalid.add((dependencies.owner, id(binding)))
    if valid_store and not invalid:
        approved.update((id(dependencies), id(dependencies.records)))
    elif not valid_store:
        invalid.add((dependencies.owner, id(dependencies.records)))
    return approved, invalid


__all__ = [
    "DependencyLeaseBatch",
    "TileDependencyLeases",
    "audit_tile_dependency_leases",
]
