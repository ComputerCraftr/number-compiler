"""Independent payload validation for retained radix action providers."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.resources.field_image_domain_audit import (
    admit_payload_root,
    indexed_record_matches,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class RadixProviderPayloadAudit:
    approved: frozenset[int]
    invalid: frozenset[tuple[int, int]]


def audit_radix_provider_payloads(
    ledger: ResourceLedger,
) -> RadixProviderPayloadAudit:
    """Validate radix action/provider stores through their owning arenas."""
    legacy_prefixes = ("number_compiler.hashlife.execution.radix_provider_consumer",)
    if not any(
        type(root).__module__.startswith(legacy_prefixes)
        for root in ledger.iter_execution_roots()
    ):
        return RadixProviderPayloadAudit(frozenset(), frozenset())

    from number_compiler.hashlife.execution.radix_consumer import (
        RadixDivisionAction,
        RadixDivisionActionArena,
        RadixDivisionActionID,
    )
    from number_compiler.hashlife.execution.radix_provider_consumer import (
        RadixProviderActionArena,
        RadixProviderActionID,
        RadixProviderAdapter,
        _RadixProviderAction,
    )

    containers = dict(ledger.iter_containers())
    roles = {row.owner: row.role for row in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    division_arenas: set[int] = set()
    provider_arenas: set[int] = set()

    for root in ledger.iter_execution_roots():
        if type(root) is RadixDivisionActionArena:
            division_stores = (
                (root._node_owner, root._nodes),
                (root._key_owner, root._keys),
                (root._compose_owner, root._children),
            )
            valid_root = (
                root.ledger is ledger
                and roles.get(root._node_owner) == "field_cell_action"
                and all(
                    containers.get(owner) is store for owner, store in division_stores
                )
            )
            if not admit_payload_root(valid_root, invalid, root._node_owner, root):
                continue
            division_arenas.add(id(root))
            all_valid = True
            for index, division_record in enumerate(root._nodes):
                valid = type(division_record) is RadixDivisionAction
                try:
                    division_record.__post_init__()
                    division_handle = RadixDivisionActionID(
                        root.owner,
                        root._KIND,
                        index,
                    )
                    valid &= root.resolve(division_handle) is division_record
                    valid &= division_record.radix == root.radix
                    valid &= root._keys.get(division_record.exponent) == index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(division_record))
                else:
                    invalid.add((root._node_owner, id(division_record)))
                    all_valid = False
            for exponent, index in root._keys.items():
                valid = (
                    type(exponent) is int
                    and exponent >= 1
                    and type(index) is int
                    and 0 <= index < len(root._nodes)
                    and root._nodes[index].exponent == exponent
                )
                if not valid:
                    invalid.add((root._key_owner, id(exponent)))
                    all_valid = False
            for index, children in root._children.items():
                valid = (
                    type(index) is int
                    and 0 <= index < len(root._nodes)
                    and type(children) is tuple
                    and len(children) == 2
                    and all(type(child) is RadixDivisionActionID for child in children)
                )
                try:
                    before, after = children
                    valid &= (
                        root.resolve(before).exponent + root.resolve(after).exponent
                        == root._nodes[index].exponent
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(children))
                else:
                    invalid.add((root._compose_owner, id(children)))
                    all_valid = False
            if all_valid:
                approved.update(id(store) for _, store in division_stores)

        elif type(root) is RadixProviderActionArena:
            provider_stores = (
                (root._node_owner, root._nodes),
                (root._key_owner, root._keys),
            )
            valid_root = (
                root.ledger is ledger
                and root.provider.ledger is ledger
                and root.divisions.ledger is ledger
                and roles.get(root._node_owner) == "field_cell_action"
                and all(
                    containers.get(owner) is store for owner, store in provider_stores
                )
            )
            if not admit_payload_root(valid_root, invalid, root._node_owner, root):
                continue
            provider_arenas.add(id(root))
            all_valid = True
            for index, provider_record in enumerate(root._nodes):
                valid = type(provider_record) is _RadixProviderAction
                try:
                    root.provider.validate_action(provider_record.provider)
                    root.divisions.resolve(provider_record.consumer)
                    provider_handle = RadixProviderActionID(
                        root.owner,
                        root._KIND,
                        index,
                    )
                    valid &= indexed_record_matches(
                        provider_handle,
                        root.resolve,
                        root._keys,
                        provider_record,
                        index,
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(provider_record))
                else:
                    invalid.add((root._node_owner, id(provider_record)))
                    all_valid = False
            if any(
                type(record) is not _RadixProviderAction
                or type(index) is not int
                or not 0 <= index < len(root._nodes)
                or root._nodes[index] != record
                for record, index in root._keys.items()
            ):
                invalid.add((root._key_owner, id(root._keys)))
                all_valid = False
            if all_valid:
                approved.update(id(store) for _, store in provider_stores)

    for root in ledger.iter_execution_roots():
        if type(root) is RadixProviderAdapter and (
            root.ledger is not ledger
            or root.sources.ledger is not ledger
            or id(root.divisions) not in division_arenas
            or id(root.actions) not in provider_arenas
        ):
            invalid.add((root.actions._node_owner, id(root)))
    return RadixProviderPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["RadixProviderPayloadAudit", "audit_radix_provider_payloads"]
