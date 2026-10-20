"""Application-owned exact inputs retained for causal result reuse."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field
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
    leases: tuple[TileLease, ...]
    _issuer: object = field(repr=False, compare=False)

    def issued_by(self, issuer: object) -> bool:
        """Check issuance authority without exposing the opaque issuer token."""
        return self._issuer is issuer


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
        self._batch_issuer = object()
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
        admitted_application = self.applications.application(application)
        if admitted_application.scheduler.tiles is not self.tiles:
            raise ValueError("causal dependency application has another tile arena")
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
        lease_slots: list[TileLease | None] = [None] * len(bindings)
        reservations = (
            (self.owner, len(bindings), 0),
            (self.tiles.lease_owner, len(bindings), 0),
        )
        self.ledger.reserve_many(reservations)
        acquired = 0
        try:
            for position, (_, tile) in enumerate(bindings):
                lease_slots[position] = self.tiles.acquire_reserved(tile)
                acquired += 1
            leases = tuple(lease for lease in lease_slots if lease is not None)
            if len(leases) != len(bindings):
                raise AssertionError("causal dependency acquisition lost a lease")
            batch = DependencyLeaseBatch(
                bindings,
                leases,
                self._batch_issuer,
            )
            for binding, lease in zip(bindings, leases, strict=True):
                self.records[binding] = lease
        except BaseException:
            for binding, slot_lease in zip(bindings, lease_slots, strict=True):
                if slot_lease is not None and self.records.get(binding) is slot_lease:
                    self.records.pop(binding, None)
            for cleanup_lease in reversed(lease_slots):
                if cleanup_lease is not None:
                    cleanup_lease.close()
            self.ledger.release(
                self.tiles.lease_owner,
                entries=len(bindings) - acquired,
            )
            self.ledger.release(self.owner, entries=len(bindings))
            raise
        return batch

    def rollback(self, batch: DependencyLeaseBatch) -> None:
        """Remove precisely the roots introduced by a failed result pin."""
        if (
            type(batch) is not DependencyLeaseBatch
            or not batch.issued_by(self._batch_issuer)
            or type(batch.bindings) is not tuple
            or type(batch.leases) is not tuple
            or len(batch.leases) != len(batch.bindings)
        ):
            raise TypeError("causal dependency rollback requires its issued batch")
        leases: list[TileLease] = []
        seen: set[tuple[int, TileID]] = set()
        for binding, issued_lease in zip(batch.bindings, batch.leases, strict=True):
            if (
                type(binding) is not tuple
                or len(binding) != 2
                or type(binding[0]) is not int
                or binding[0] < 0
                or type(binding[1]) is not TileID
            ):
                raise ValueError("causal dependency rollback binding is malformed")
            if binding in seen:
                raise ValueError(
                    "causal dependency rollback contains duplicate bindings"
                )
            seen.add(binding)
            lease = self.records.get(binding)
            if (
                type(issued_lease) is not TileLease
                or type(lease) is not TileLease
                or lease is not issued_lease
                or lease.tile != binding[1]
            ):
                raise ValueError("causal dependency rollback lost a binding")
            leases.append(lease)
        count = len(leases)
        if (
            self.ledger.account_usage(self.owner)[0] < count
            or self.ledger.account_usage(self.tiles.lease_owner)[0] < count
        ):
            raise ValueError("causal dependency rollback accounting is inconsistent")
        for binding, lease in reversed(tuple(zip(batch.bindings, leases, strict=True))):
            try:
                removed = self.records.pop(binding)
            except BaseException:
                if binding not in self.records:
                    self.records[binding] = lease
                raise
            if removed is not lease:
                if binding not in self.records:
                    self.records[binding] = removed
                raise ValueError("causal dependency changed during rollback")
            try:
                lease.close()
            except BaseException:
                if lease.audit_snapshot().closed:
                    self.ledger.release(self.owner, entries=1)
                else:
                    self.records[binding] = lease
                raise
            self.ledger.release(self.owner, entries=1)

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
                if not lease.audit_snapshot().closed:
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
            )
            if (
                type(application) is int
                and application >= 0
                and type(tile) is TileID
                and lease.tile == tile
            ):
                dependencies.tiles.resolve(tile)
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
