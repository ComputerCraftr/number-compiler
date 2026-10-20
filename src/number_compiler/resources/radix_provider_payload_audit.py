"""Independent payload validation for retained radix action providers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TypeGuard

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.hashlife.execution.radix_consumer import RadixDivisionActionID
from number_compiler.resources.field_image_domain_audit import admit_payload_root
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class RadixProviderPayloadAudit:
    approved: frozenset[int]
    invalid: frozenset[tuple[int, int]]


def audit_radix_provider_payloads(
    ledger: ResourceLedger,
) -> RadixProviderPayloadAudit:
    """Validate radix action/provider stores through immutable owner snapshots."""
    legacy_prefixes = ("number_compiler.hashlife.execution.radix_provider_consumer",)
    roots = tuple(ledger.iter_execution_roots())
    if not any(type(root).__module__.startswith(legacy_prefixes) for root in roots):
        return RadixProviderPayloadAudit(frozenset(), frozenset())

    from number_compiler.hashlife.execution.radix_consumer import (
        RadixDivisionAction,
        RadixDivisionActionArena,
    )
    from number_compiler.hashlife.execution.radix_provider_consumer import (
        RadixProviderActionArena,
        RadixProviderActionID,
        RadixProviderActionRecord,
        RadixProviderAdapter,
    )

    containers = dict(ledger.iter_containers())
    roles = {row.owner: row.role for row in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    division_arenas: set[int] = set()
    provider_arenas: set[int] = set()

    for root in roots:
        if type(root) is RadixDivisionActionArena:
            division_snapshot = root.audit_snapshot()
            division_stores = (
                (division_snapshot.node_owner, division_snapshot.node_store_identity),
                (division_snapshot.key_owner, division_snapshot.key_store_identity),
                (
                    division_snapshot.composition_owner,
                    division_snapshot.composition_store_identity,
                ),
            )
            valid_root = (
                division_snapshot.ledger is ledger
                and roles.get(division_snapshot.node_owner) == "field_cell_action"
                and _stores_match(containers, division_stores)
            )
            if not admit_payload_root(
                valid_root, invalid, division_snapshot.node_owner, root
            ):
                continue
            division_arenas.add(id(root))
            all_valid = True
            for division_node_index, division_record in enumerate(
                division_snapshot.nodes
            ):
                valid = type(division_record) is RadixDivisionAction
                try:
                    division_record.__post_init__()
                    division_handle = RadixDivisionActionID(
                        division_snapshot.owner,
                        division_snapshot.kind,
                        division_node_index,
                    )
                    valid &= root.resolve(division_handle) is division_record
                    valid &= division_record.radix == division_snapshot.radix
                    valid &= (
                        root.exponent_index(division_record.exponent)
                        == division_node_index
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(division_record))
                else:
                    invalid.add((division_snapshot.node_owner, id(division_record)))
                    all_valid = False
            for exponent, key_index in division_snapshot.key_rows:
                valid = (
                    type(exponent) is int
                    and exponent >= 1
                    and type(key_index) is int
                    and 0 <= key_index < len(division_snapshot.nodes)
                    and division_snapshot.nodes[key_index].exponent == exponent
                )
                if not valid:
                    invalid.add((division_snapshot.key_owner, id(exponent)))
                    all_valid = False
            for composition_index, children in division_snapshot.composition_rows:
                valid = False
                if (
                    type(composition_index) is int
                    and 0 <= composition_index < len(division_snapshot.nodes)
                    and _is_division_children(children)
                ):
                    before, after = children
                    try:
                        valid = (
                            root.resolve(before).exponent + root.resolve(after).exponent
                            == division_snapshot.nodes[composition_index].exponent
                        )
                    except (TypeError, ValueError, IndexError, AttributeError):
                        valid = False
                if valid:
                    approved.add(id(children))
                else:
                    invalid.add((division_snapshot.composition_owner, id(children)))
                    all_valid = False
            if all_valid:
                approved.update(store_identity for _, store_identity in division_stores)

        elif type(root) is RadixProviderActionArena:
            provider_snapshot = root.audit_snapshot()
            provider_stores = (
                (provider_snapshot.node_owner, provider_snapshot.node_store_identity),
                (provider_snapshot.key_owner, provider_snapshot.key_store_identity),
            )
            valid_root = (
                provider_snapshot.ledger is ledger
                and root.provider.ledger is ledger
                and root.divisions.ledger is ledger
                and roles.get(provider_snapshot.node_owner) == "field_cell_action"
                and _stores_match(containers, provider_stores)
            )
            if not admit_payload_root(
                valid_root, invalid, provider_snapshot.node_owner, root
            ):
                continue
            provider_arenas.add(id(root))
            all_valid = True
            for provider_node_index, provider_record in enumerate(
                provider_snapshot.nodes
            ):
                valid = type(provider_record) is RadixProviderActionRecord
                try:
                    root.provider.validate_action(provider_record.provider)
                    root.divisions.resolve(provider_record.consumer)
                    provider_handle = RadixProviderActionID(
                        provider_snapshot.owner,
                        provider_snapshot.kind,
                        provider_node_index,
                    )
                    valid &= root.resolve(provider_handle) is provider_record
                    valid &= root.record_index(provider_record) == provider_node_index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(provider_record))
                else:
                    invalid.add((provider_snapshot.node_owner, id(provider_record)))
                    all_valid = False
            for key_record, provider_key_index in provider_snapshot.key_rows:
                valid = (
                    type(key_record) is RadixProviderActionRecord
                    and type(provider_key_index) is int
                    and 0 <= provider_key_index < len(provider_snapshot.nodes)
                    and provider_snapshot.nodes[provider_key_index] == key_record
                )
                if not valid:
                    invalid.add((provider_snapshot.key_owner, id(key_record)))
                    all_valid = False
            if all_valid:
                approved.update(store_identity for _, store_identity in provider_stores)

    for root in roots:
        if type(root) is RadixProviderAdapter and (
            root.ledger is not ledger
            or root.sources.ledger is not ledger
            or id(root.divisions) not in division_arenas
            or id(root.actions) not in provider_arenas
        ):
            adapter_snapshot = root.actions.audit_snapshot()
            invalid.add((adapter_snapshot.node_owner, id(root)))
    return RadixProviderPayloadAudit(frozenset(approved), frozenset(invalid))


def _stores_match(
    containers: dict[int, object], stores: tuple[tuple[int, int], ...]
) -> bool:
    return all(
        (container := containers.get(owner)) is not None
        and id(container) == store_identity
        for owner, store_identity in stores
    )


def _is_division_children(
    value: object,
) -> TypeGuard[tuple[RadixDivisionActionID, RadixDivisionActionID]]:
    return (
        is_exact_object_tuple(value)
        and len(value) == 2
        and type(value[0]) is RadixDivisionActionID
        and type(value[1]) is RadixDivisionActionID
    )


__all__ = ["RadixProviderPayloadAudit", "audit_radix_provider_payloads"]
