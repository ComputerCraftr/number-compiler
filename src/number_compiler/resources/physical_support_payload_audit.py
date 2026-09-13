"""Independent ownership audit for retained Collatz shadow-support programs."""

from __future__ import annotations

from dataclasses import dataclass
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class PhysicalSupportPayloadAudit:
    approved: frozenset[int]
    invalid: frozenset[tuple[int, int]]


def audit_physical_support_payloads(
    ledger: ResourceLedger,
) -> PhysicalSupportPayloadAudit:
    from number_compiler.sequences.collatz.physical_support import (
        PhysicalSupport,
        PhysicalSupportArena,
    )

    containers = dict(ledger.iter_containers())
    inventory = {item.owner: item for item in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in ledger.iter_execution_roots():
        if type(root) is not PhysicalSupportArena:
            continue
        raw_owners = root._node_owner, root._join_owner, root._concat_owner
        if any(type(owner) is not int for owner in raw_owners):
            invalid.add((-1, id(root)))
            continue
        node_owner, join_owner, concat_owner = raw_owners
        stores = (
            (node_owner, root._nodes, "physical_shadow_support"),
            (
                join_owner,
                root._joins,
                "physical_shadow_support_composition",
            ),
            (
                concat_owner,
                root._concats,
                "physical_shadow_support_composition",
            ),
        )
        valid = (
            root.ledger is ledger
            and root._store_ledger is ledger
            and all(
                type(owner) is int
                and containers.get(owner) is store
                and inventory[owner].role == role
                and inventory[owner].entries == len(store)
                for owner, store, role in stores
            )
        )
        for index, node in enumerate(root._nodes):
            try:
                valid &= type(node) is PhysicalSupport and node.node_id == index
                root.validate(node)
            except (TypeError, ValueError, AttributeError, IndexError):
                valid = False
                invalid.add((node_owner, id(node)))
            else:
                approved.add(id(node))
        for owner, store in (
            (join_owner, root._joins),
            (concat_owner, root._concats),
        ):
            for key, node in store.items():
                try:
                    valid &= (
                        type(key) is tuple
                        and len(key) == 2
                        and all(type(part) is int for part in key)
                        and type(node) is PhysicalSupport
                    )
                    root.validate(node)
                except (TypeError, ValueError, AttributeError, IndexError):
                    valid = False
                    invalid.update(((owner, id(key)), (owner, id(node))))
                else:
                    approved.update((id(key), id(node)))
        if valid:
            approved.update((id(root), *(id(store) for _, store, _ in stores)))
        else:
            invalid.add((node_owner, id(root)))
    return PhysicalSupportPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["PhysicalSupportPayloadAudit", "audit_physical_support_payloads"]
