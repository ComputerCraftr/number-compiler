"""Read-only inventory of the canonical local-interface quotient arena."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.interfaces.semantic_structures import (
    DiamondKey,
    LocalInterfaceID,
    MacroComponents,
    MacroInterface,
    QuotientRecord,
)


def audit_quotient_arena(
    root: DiamondQuotientArena,
    ledger: object,
    containers: Mapping[int, object],
) -> tuple[set[int], set[tuple[int, int]]]:
    """Validate quotient stores without importing retired image executors."""
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    snapshot = root.audit_snapshot()
    stores = (
        (snapshot.signature_owner, snapshot.signatures),
        (snapshot.signature_key_owner, snapshot.signature_keys),
        (snapshot.node_owner, snapshot.nodes),
        (snapshot.key_owner, snapshot.keys),
        (snapshot.normalization_owner, snapshot.normalizations),
        (snapshot.binding_owner, snapshot.parents),
    )
    all_valid = (
        snapshot.ledger is ledger
        and type(snapshot.next_node) is int
        and snapshot.next_node >= 0
        and len(snapshot.nodes) <= snapshot.next_node
        and len(snapshot.keys) == len(snapshot.nodes)
        and all(
            type(local_id) is int and 0 <= local_id < snapshot.next_node
            for local_id in snapshot.nodes
        )
        and all(containers.get(owner) is store for owner, store in stores)
    )
    for index, signature_record in enumerate(snapshot.signatures):
        valid = type(signature_record) is MacroInterface
        retained: object = None
        signature_handle: PortSignatureID | None = None
        try:
            root.validate_interface_record(signature_record)
            signature_handle = PortSignatureID(
                snapshot.owner, "diamond-semantic-signature", index
            )
            valid &= root.interface(signature_handle) is signature_record
            valid &= snapshot.signature_keys.get(signature_record) == signature_handle
            retained = snapshot.signature_keys.get(signature_record)
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        if valid and signature_handle is not None:
            approved.update((id(signature_record), id(signature_handle), id(retained)))
        else:
            invalid.add((snapshot.signature_owner, id(signature_record)))
            all_valid = False
    for index, quotient_record in snapshot.nodes.items():
        valid = type(quotient_record) is QuotientRecord
        quotient_handle: LocalInterfaceID | None = None
        try:
            valid &= type(quotient_record.components) is MacroComponents
            root.validate_quotient_record(quotient_record)
            quotient_handle = LocalInterfaceID(
                snapshot.owner, "diamond-quotient", index
            )
            valid &= root.resolve(quotient_handle) is quotient_record
            valid &= snapshot.keys.get(quotient_record) == quotient_handle
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            valid = False
        if valid and quotient_handle is not None:
            approved.update(
                (
                    id(quotient_record),
                    id(quotient_record.components),
                    id(quotient_handle),
                    id(quotient_record.signature),
                )
            )
        else:
            invalid.add((snapshot.node_owner, id(quotient_record)))
            all_valid = False
    for normalization_request, result in snapshot.normalizations.items():
        valid = type(normalization_request) is QuotientRecord
        try:
            root.validate_quotient_record(normalization_request)
            valid &= root.resolve(result).signature == normalization_request.signature
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        if valid:
            approved.update(
                (
                    id(normalization_request),
                    id(normalization_request.components),
                    id(result),
                )
            )
        else:
            invalid.add((snapshot.normalization_owner, id(normalization_request)))
            all_valid = False
    for parent_request, result in snapshot.parents.items():
        valid = type(parent_request) is DiamondKey
        try:
            root.validate_parent_key(parent_request)
            valid &= root.resolve(result).signature == parent_request.signature
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        if valid:
            approved.update((id(parent_request), id(result)))
        else:
            invalid.add((snapshot.binding_owner, id(parent_request)))
            all_valid = False
    if all_valid:
        approved.update(id(store) for _, store in stores)
    return approved, invalid


__all__ = ["audit_quotient_arena"]
