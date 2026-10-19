"""Independent payload audit for finite temporal-composition caches."""

from __future__ import annotations

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit,
)


def audit_cocycle_temporal_payloads(
    ledger: ResourceLedger,
) -> PhysicalSupportPayloadAudit:
    """Validate paired cache publications without recomputing composition."""
    from devtools.experiments.reverse_add.cocycle_temporal import (
        CocycleCompositionEntry,
        CocycleCompositionKey,
        CocycleTemporalArena,
    )

    containers = dict(ledger.iter_containers())
    inventory = {row.owner: row for row in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in ledger.iter_execution_roots():
        if type(root) is not CocycleTemporalArena:
            continue
        try:
            snapshot = root.audit_snapshot()
        except (TypeError, ValueError, AttributeError, RuntimeError):
            invalid.add((-1, id(root)))
            continue

        cache = snapshot.composition_cache
        seals = snapshot.composition_seals
        cache_data = cache.container
        seal_data = seals.container
        owner = cache.owner if type(cache.owner) is int else -1
        seal_owner = seals.owner if type(seals.owner) is int else -1
        owner_row = inventory.get(owner)
        seal_owner_row = inventory.get(seal_owner)
        root_approved: set[int] = {
            id(root),
            id(snapshot.composition_cache_identity),
            id(snapshot.composition_seals_identity),
            id(cache_data),
            id(seal_data),
        }
        valid = (
            snapshot.ledger is ledger
            and snapshot.bits.ledger is ledger
            and snapshot.bits is snapshot.cocycles.bits
            and snapshot.root_fields
            == frozenset(
                {
                    "cocycles",
                    "bits",
                    "ledger",
                    "primitive_successors",
                    "temporal_compositions",
                    "temporal_composition_cache_hits",
                    "_composition_cache",
                    "_composition_seals",
                    "_next_composition_entry",
                }
            )
            and all(
                type(value) is int and value >= 0
                for value in (
                    snapshot.primitive_successors,
                    snapshot.temporal_compositions,
                    snapshot.temporal_composition_cache_hits,
                )
            )
            and cache.ledger is ledger
            and seals.ledger is ledger
            and owner != seal_owner
            and type(cache.owner) is int
            and type(seals.owner) is int
            and containers.get(owner) is cache_data
            and containers.get(seal_owner) is seal_data
            and owner_row is not None
            and seal_owner_row is not None
            and owner_row.role == "query_memo"
            and seal_owner_row.role == "query_memo"
            and owner_row.entries == len(cache_data)
            and seal_owner_row.entries == len(seal_data)
            and owner_row.accounting_delta == 0
            and seal_owner_row.accounting_delta == 0
            and len(cache_data) == len(seal_data)
            and type(snapshot.composition_cache_limit) is int
            and snapshot.composition_cache_limit == 1024
            and len(cache_data) <= snapshot.composition_cache_limit
            and type(snapshot.next_composition_entry) is int
            and snapshot.next_composition_entry >= len(cache_data)
        )
        entry_ids: set[int] = set()
        try:
            for key, entry_value in cache_data.items():
                seal_value = seal_data.get(key)
                if (
                    type(key) is CocycleCompositionKey
                    and type(entry_value) is CocycleCompositionEntry
                    and type(seal_value) is tuple
                ):
                    bound = root.audit_validate_entry(
                        key,
                        entry_value,
                        seal_value,
                        snapshot.next_composition_entry,
                    )
                    if bound and entry_value.entry_id not in entry_ids:
                        entry_ids.add(entry_value.entry_id)
                        root_approved.update(
                            (
                                id(key),
                                id(entry_value),
                                id(entry_value.result),
                                id(seal_value),
                            )
                        )
                    else:
                        bound = False
                else:
                    bound = False
                valid &= bound
            valid &= set(cache_data) == set(seal_data)
        except (TypeError, ValueError, KeyError, IndexError, AttributeError):
            valid = False
        if valid:
            approved.update(root_approved)
        else:
            invalid.add((owner, id(root)))
            invalid.add((seal_owner, id(root)))
    return PhysicalSupportPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["audit_cocycle_temporal_payloads"]
