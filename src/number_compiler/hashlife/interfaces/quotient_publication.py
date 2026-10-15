"""Atomic publication of complete local interfaces and their occurrence bindings."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.reverse_port_functions import ReversePortFunction
from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
)
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondKey,
        DiamondQuotientArena,
        DiamondQuotientID,
        QuotientRecord,
    )
    from number_compiler.hashlife.interfaces.semantic_structure_publication import (
        PreparedStructures,
    )
    from number_compiler.hashlife.tiles.tile_result_records import SpatialInterfaceKey
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena


@dataclass(frozen=True, slots=True)
class SpatialQuotientBinding:
    """One transient cross-owner publication target; never retained as payload."""

    results: CompletedResultArena
    key: SpatialInterfaceKey


def retained_record_nodes(record: QuotientRecord) -> int:
    """Charge inline bounded function slots separately from the canonical record.

    These are retained arithmetic slots, not a claim about unique DAG nodes.
    Repeated references to the same channel object inside one record are charged
    once; independently constructed equal objects still occupy backing storage.
    """
    seen: set[int] = set()
    result = 1
    for component in record.components.functions():
        if type(component) is ReversePortFunction and id(component) not in seen:
            seen.add(id(component))
            result += (
                1 + component.retained_coefficient_slots + component.retained_limb_slots
            )
    sectors = record.components.reverse_sectors
    if type(sectors) is ReverseCarrySectorTransfer:
        result += sectors.retained_slots()
    return result


def publish_quotient(
    self: DiamondQuotientArena,
    record: QuotientRecord,
    key: DiamondKey | None,
    prepared: PreparedStructures | None = None,
    *,
    alias: QuotientRecord | None = None,
    spatial: SpatialQuotientBinding | None = None,
) -> DiamondQuotientID:
    from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID

    found = self._keys.get(record)
    if spatial is not None:
        from number_compiler.hashlife.tiles.tile_results import CompletedResultArena

        if type(spatial) is not SpatialQuotientBinding:
            raise TypeError("quotient publication has another spatial binding sort")
        results = spatial.results
        if type(results) is not CompletedResultArena:
            raise TypeError("quotient spatial binding requires the result memo owner")
        if results.interfaces is not self or results.ledger is not self.ledger:
            raise ValueError("quotient spatial binding belongs to another index")
        results._validate_spatial_key(spatial.key)
        spatial_value = results._memo.get(spatial.key)
        if spatial_value is not None:
            if type(spatial_value) is not LocalInterfaceID:
                raise TypeError("spatial interface memo has another value sort")
            spatial_found = spatial_value
            results._validate_spatial_result(spatial.key, spatial_found)
            if self.resolve(spatial_found) != record:
                if prepared is not None:
                    prepared.cancel()
                raise ValueError("spatial request already has another semantic result")
            if prepared is not None:
                prepared.cancel()
            results.ledger.bump(_shared_keys.SPATIAL_INTERFACE_COMPOSITION_LATE_ALIASES)
            return spatial_found
    if key is not None and key in self._parents:
        existing = self._parents[key]
        if existing != found:
            if prepared is not None:
                prepared.cancel()
            raise ValueError("diamond request already has a different semantic result")
        if prepared is not None:
            prepared.cancel()
        return existing
    reservations: list[tuple[int, int, int]] = []
    new_node = found is None
    if new_node:
        reservations.extend(
            (
                (self._node_owner, 1, retained_record_nodes(record)),
                (self._key_owner, 1, 0),
            )
        )
    publish_alias = (
        alias is not None and alias != record and alias not in self._normalizations
    )
    if publish_alias:
        reservations.append((self._normalization_owner, 1, 0))
    if key is not None:
        reservations.append((self._binding_owner, 1, 0))
    if spatial is not None:
        reservations.append((spatial.results._memo_owner, 1, 0))
    local_id: int | None = None
    reserved = False
    try:
        if prepared is not None:
            prepared.reserve_with(tuple(reservations))
        else:
            self.ledger.reserve_many(reservations)
        reserved = True
        if new_node:
            local_id = self._next_node
            self._next_node += 1
            found = LocalInterfaceID(self.owner, "diamond-quotient", local_id)
            self._nodes[local_id] = record
            self._keys[record] = found
        assert found is not None
        if publish_alias:
            assert alias is not None
            self._normalizations[alias] = found
        if key is not None:
            self._parents[key] = found
        if spatial is not None:
            spatial.results._validate_spatial_result(spatial.key, found)
            spatial.results._memo[spatial.key] = found
        if prepared is not None:
            prepared.publish_reserved()
    except BaseException:
        if spatial is not None:
            spatial.results._memo.pop(spatial.key, None)
        if key is not None:
            self._parents.pop(key, None)
        if publish_alias:
            assert alias is not None
            self._normalizations.pop(alias, None)
        if local_id is not None:
            self._keys.pop(record, None)
            self._nodes.pop(local_id, None)
        if reserved and (prepared is None or prepared.functions.transaction is None):
            for owner, entries, nodes in reservations:
                self.ledger.release(owner, entries=entries, nodes=nodes)
        self.ledger.bump(_interfaces_keys.QUOTIENT_PUBLICATION_FAILURES)
        raise
    finally:
        if prepared is not None:
            prepared.cancel()
    if new_node:
        self.ledger.bump(_interfaces_keys.QUOTIENT_SEMANTIC_INTERNER_EVALUATIONS)
    elif prepared is not None:
        self.ledger.bump(_interfaces_keys.QUOTIENT_SEMANTIC_INTERNER_HITS)
        self.ledger.bump(_interfaces_keys.QUOTIENT_LATE_DUPLICATE_REDUCTIONS)
    if key is not None:
        self.ledger.bump(_interfaces_keys.QUOTIENT_PARENT_PUBLICATIONS)
    if spatial is not None:
        spatial.results.ledger.bump(
            _shared_keys.SPATIAL_INTERFACE_COMPOSITION_PUBLICATIONS
        )
    return found
