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
        CocycleTemporalArena,
        _CompositionEntry,
        _CompositionKey,
    )

    containers = dict(ledger.iter_containers())
    inventory = {row.owner: row for row in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in ledger.iter_execution_roots():
        if type(root) is not CocycleTemporalArena:
            continue
        owner = root._composition_cache.owner
        seal_owner = root._composition_seals.owner
        owner_row = inventory.get(owner)
        seal_owner_row = inventory.get(seal_owner)
        root_approved: set[int] = {
            id(root),
            id(root._composition_cache),
            id(root._composition_seals),
            id(root._composition_cache._data),
            id(root._composition_seals._data),
        }
        valid = (
            root.ledger is ledger
            and root.bits.ledger is ledger
            and root.bits is root.cocycles.bits
            and set(vars(root))
            == {
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
            and all(
                type(value) is int and value >= 0
                for value in (
                    root.primitive_successors,
                    root.temporal_compositions,
                    root.temporal_composition_cache_hits,
                )
            )
            and root._composition_cache.ledger is ledger
            and root._composition_seals.ledger is ledger
            and owner != seal_owner
            and type(owner) is int
            and type(seal_owner) is int
            and containers.get(owner) is root._composition_cache._data
            and containers.get(seal_owner) is root._composition_seals._data
            and owner_row is not None
            and seal_owner_row is not None
            and owner_row.role == "query_memo"
            and seal_owner_row.role == "query_memo"
            and owner_row.entries == len(root._composition_cache)
            and seal_owner_row.entries == len(root._composition_seals)
            and owner_row.accounting_delta == 0
            and seal_owner_row.accounting_delta == 0
            and len(root._composition_cache) == len(root._composition_seals)
            and type(root._COMPOSITION_CACHE_LIMIT) is int
            and root._COMPOSITION_CACHE_LIMIT == 1024
            and len(root._composition_cache) <= root._COMPOSITION_CACHE_LIMIT
            and type(root._next_composition_entry) is int
            and root._next_composition_entry >= len(root._composition_cache)
        )
        entry_ids: set[int] = set()
        try:
            for key, entry in root._composition_cache.items():
                seal = root._composition_seals.get(key)
                bound = (
                    type(key) is _CompositionKey
                    and type(entry) is _CompositionEntry
                    and entry.key == key
                    and type(entry.entry_id) is int
                    and 0 <= entry.entry_id < root._next_composition_entry
                    and entry.entry_id not in entry_ids
                    and type(seal) is tuple
                    and seal == root._entry_seal(entry)
                    and entry.result.events == key.before_events + key.after_events
                )
                if bound:
                    # Rebuild only the immutable action envelopes. The handles
                    # remain authenticated by the owning finite arenas.
                    from devtools.experiments.reverse_add.cocycle_temporal import (
                        CocycleAction,
                    )

                    before_action = CocycleAction(
                        key.before_ports,
                        key.before_outputs,
                        key.before_cocycles,
                        key.before_admissible,
                        key.before_events,
                    )
                    after_action = CocycleAction(
                        key.after_ports,
                        key.after_outputs,
                        key.after_cocycles,
                        key.after_admissible,
                        key.after_events,
                    )
                    root._validate(before_action)
                    root._validate(after_action)
                    root._validate(entry.result)
                valid &= bound
                if bound:
                    entry_ids.add(entry.entry_id)
                    root_approved.update(
                        (id(key), id(entry), id(entry.result), id(seal))
                    )
            valid &= set(root._composition_cache) == set(root._composition_seals)
        except (TypeError, ValueError, KeyError, IndexError, AttributeError):
            valid = False
        if valid:
            approved.update(root_approved)
        else:
            invalid.add((owner, id(root)))
            invalid.add((seal_owner, id(root)))
    return PhysicalSupportPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["audit_cocycle_temporal_payloads"]
