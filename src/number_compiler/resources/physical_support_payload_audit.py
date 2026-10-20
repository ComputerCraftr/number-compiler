"""Independent ownership audit for retained ordered Boolean support programs."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.input_validation import (
    is_runtime_instance,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_containers import audit_mapping_items


@dataclass(frozen=True, slots=True)
class PhysicalSupportPayloadAudit:
    approved: frozenset[int]
    invalid: frozenset[tuple[int, int]]


def audit_physical_support_payloads(
    ledger: ResourceLedger,
) -> PhysicalSupportPayloadAudit:
    from number_compiler.hashlife.tiles.ordered_boolean_support import (
        OrderedBooleanSupport,
        OrderedBooleanSupportArena,
    )

    containers = dict(ledger.iter_containers())
    inventory = {item.owner: item for item in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in ledger.iter_execution_roots():
        if not isinstance(root, OrderedBooleanSupportArena):
            continue
        snapshot = root.audit_snapshot()
        raw_owners = snapshot.node_owner, snapshot.join_owner, snapshot.concat_owner
        if any(type(owner) is not int for owner in raw_owners):
            invalid.add((-1, id(root)))
            continue
        node_owner, join_owner, concat_owner = raw_owners
        stores = (
            (
                node_owner,
                snapshot.node_store_identity,
                snapshot.nodes,
                "ordered_boolean_support",
            ),
            (
                join_owner,
                snapshot.join_store_identity,
                snapshot.joins,
                "ordered_boolean_support_composition",
            ),
            (
                concat_owner,
                snapshot.concat_store_identity,
                snapshot.concats,
                "ordered_boolean_support_composition",
            ),
        )
        valid = (
            root.ledger is ledger
            and snapshot.storage_ledger is ledger
            and all(
                type(owner) is int
                and (container := containers.get(owner)) is not None
                and id(container) == store_identity
                and inventory[owner].role == role
                and inventory[owner].entries == len(store)
                for owner, store_identity, store, role in stores
            )
        )
        for index, node in enumerate(snapshot.nodes):
            try:
                valid &= (
                    is_runtime_instance(node, OrderedBooleanSupport)
                    and type(node) is snapshot.node_type
                    and node.node_id == index
                )
                root.validate(node)
            except (TypeError, ValueError, AttributeError, IndexError):
                valid = False
                invalid.add((node_owner, id(node)))
            else:
                approved.add(id(node))
        for owner, store in (
            (join_owner, snapshot.joins),
            (concat_owner, snapshot.concats),
        ):
            for key, node in audit_mapping_items(store):
                try:
                    valid &= (
                        type(key) is tuple
                        and len(key) == 2
                        and all(type(part) is int for part in key)
                        and is_runtime_instance(node, OrderedBooleanSupport)
                        and type(node) is snapshot.node_type
                    )
                    root.validate(node)
                except (TypeError, ValueError, AttributeError, IndexError):
                    valid = False
                    invalid.update(((owner, id(key)), (owner, id(node))))
                else:
                    approved.update((id(key), id(node)))
        if valid:
            approved.update(
                (id(root), *(store_identity for _, store_identity, _, _ in stores))
            )
        else:
            invalid.add((node_owner, id(root)))
    return PhysicalSupportPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["PhysicalSupportPayloadAudit", "audit_physical_support_payloads"]
