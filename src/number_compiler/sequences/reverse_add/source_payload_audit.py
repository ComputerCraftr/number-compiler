"""Independent retained-payload audit for the reverse/add source adapter."""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence

from number_compiler.resources.ledger import ResourceInventory, ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
)
from number_compiler.resources.reverse_source_payload_audit import (
    ReverseSourcePayloadAudit,
)
from number_compiler.sequences.reverse_add.source_audit_bindings import (
    nested_source_store_bindings,
    source_audit_owners,
)
from number_compiler.sequences.reverse_add.source_workspace_payload_audit import (
    audit_reverse_source_workspaces,
    store_valid_for_audit,
)


def audit_reverse_source_payloads(
    ledger: ResourceLedger,
    roots: tuple[object, ...],
    containers: Mapping[int, object],
) -> ReverseSourcePayloadAudit:
    """Validate reverse source records without constructing or evaluating images."""
    # Keep unrelated ledgers independent of the reverse runtime imports below.
    # This is only an import gate; every admitted root still passes the exact
    # arena, owner, and authority checks in the audit body.
    if not any(
        type(root).__module__.startswith("number_compiler.sequences.reverse_add.")
        for root in roots
    ):
        return ReverseSourcePayloadAudit(frozenset(), frozenset(), frozenset())

    from number_compiler.arithmetic.carry.carry_monoid import CarryFn
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

    owners = source_audit_owners(roots)
    inventory: dict[int, ResourceInventory] = {}
    for owner in owners:
        try:
            inventory[owner] = ledger.inventory_owner(owner)
        except (IndexError, TypeError, ValueError):
            continue
    containers = {owner: containers.get(owner) for owner in owners}
    approved: set[int] = set()
    recognized: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    # Spatial carry products are projections, not source or successor identities.
    # Audit geometry and source ownership without invoking any runtime evaluator.
    for ports in roots:
        if type(ports) is not SourceCarryPorts:
            continue
        port_snapshot = ports.audit_snapshot()
        cache = port_snapshot.cache
        owner = cache.owner
        port_authority = port_snapshot.authority
        port_source = port_snapshot.source
        valid_ports = (
            type(port_authority) is tuple
            and len(port_authority) == 10
            and port_authority[0] is port_source
            and type(port_source) is ExactSource
            and port_source.digits is port_authority[1]
            and port_source.base == port_authority[2]
            and port_source.orbit == port_authority[3]
            and port_source.blank == port_authority[4]
            and port_source.extent == port_authority[5]
            and port_source.alphabet_size == port_authority[6]
            and port_snapshot.ledger is ledger
            and port_authority[7] is ledger
            and port_authority[8] is port_snapshot.cache_identity
            and port_authority[9] == owner
            and port_snapshot.workspace_owner == port_snapshot.workspace_authority
            and port_snapshot.width == len(port_source.digits)
            and store_valid_for_audit(
                ledger,
                owner,
                port_snapshot.cache_identity,
                "reverse_source_carry_interval",
                containers,
                inventory,
            )
            and cache.container is port_snapshot.audit_cache
        )
        recognized.add(id(ports))
        for key, value in cache.container.items():
            recognized.add(id(key))
            geometry_valid = (
                type(key) is tuple
                and len(key) == 3
                and all(type(item) is int for item in key)
                and key[0] in (1, 2)
                and key[1] >= 0
                and key[2] > 0
                and key[2] & (key[2] - 1) == 0
                and key[1] % key[2] == 0
                and key[1] + key[2] <= port_snapshot.width + int(key[0] == 2)
                and type(value) is CarryFn
            )
            if valid_ports and geometry_valid:
                approved.update((id(key), id(value)))
            else:
                invalid.add((owner, id(key)))
                invalid.add((owner, id(value)))
        if valid_ports:
            approved.update((id(ports), id(cache.container)))
        else:
            invalid.add((owner, id(ports)))
    workspace_approved, workspace_recognized, workspace_invalid = (
        audit_reverse_source_workspaces(ledger, roots, containers, inventory)
    )
    approved.update(workspace_approved)
    recognized.update(workspace_recognized)
    invalid.update(workspace_invalid)
    return ReverseSourcePayloadAudit(
        frozenset(approved), frozenset(recognized), frozenset(invalid)
    )


def audit_reverse_source_owner(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Return source-image evidence only from this root's bound stores."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("reverse source audit requires its resource ledger")
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
    from number_compiler.sequences.reverse_add.source_workspace import (
        ReverseSourceImageWorkspace,
    )

    bindings: tuple[PayloadAuditStoreBinding, ...]
    roots: tuple[object, ...]
    if type(root) is SourceCarryPorts:
        bindings = (
            PayloadAuditStoreBinding(
                root.audit_snapshot().cache.owner,
                "_audit_cache",
                "reverse_source_carry_interval",
            ),
        )
        roots = (root,)
    elif type(root) is ReverseSourceImageWorkspace:
        bindings = (
            PayloadAuditStoreBinding(
                root.actions.audit_snapshot().nodes.owner,
                "_audit_action_nodes",
                "reverse_source_action",
            ),
            PayloadAuditStoreBinding(
                root.actions.audit_snapshot().normal.owner,
                "_audit_action_normal",
                "reverse_source_action_normal_form",
            ),
            PayloadAuditStoreBinding(
                root.actions.audit_snapshot().sources.owner,
                "_audit_sources",
                "reverse_original_source",
            ),
            PayloadAuditStoreBinding(
                root.actions.audit_snapshot().workspace_owner,
                "_audit_action_workspace",
                "reverse_source_action_workspace",
            ),
            PayloadAuditStoreBinding(
                root.adapter.audit_snapshot().recursive_occurrences.owner,
                "_audit_recursive_occurrences",
                "reverse_recursive_occurrence_binding",
            ),
            PayloadAuditStoreBinding(
                root.audit_snapshot().pointed_gt_banks.owner,
                "_audit_pointed_gt_banks",
                "reverse_source_pointed_gt_bank",
            ),
            *nested_source_store_bindings(root),
        )
        ports = root.adapter.published_ports
        roots = (root,) if ports is None else (root, ports)
    else:
        return PayloadAuditContribution()

    owners = source_audit_owners(roots)
    containers: dict[int, object] = {}
    for owner in owners:
        try:
            containers[owner] = ledger.registered_container(owner)
        except (IndexError, RuntimeError, TypeError, ValueError):
            continue
    results = audit_reverse_source_payloads(ledger, roots, containers)
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    for binding in bindings:
        owner, attribute = binding.owner, binding.attribute
        store = getattr(root, attribute)
        if isinstance(store, Mapping):
            values: Iterable[object] = (
                value for pair in store.items() for value in pair
            )
        elif isinstance(store, Sequence) and not isinstance(
            store, (str, bytes, bytearray)
        ):
            values = store
        else:
            values = ()
        for value in values:
            if id(value) in results.approved:
                approved.append(PayloadAuditEntry(owner, value))
            if (owner, id(value)) in results.invalid:
                invalid.append(PayloadAuditEntry(owner, value))
    if results.invalid and not invalid:
        invalid.append(PayloadAuditEntry(bindings[0].owner, root))
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = [
    "ReverseSourcePayloadAudit",
    "audit_reverse_source_owner",
    "audit_reverse_source_payloads",
]
