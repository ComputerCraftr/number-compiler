"""Read-only inventory of the canonical local-interface quotient arena."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.interfaces.diamond_quotient import (
    DiamondKey,
    DiamondQuotientArena,
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
    stores = (
        (root._signature_owner, root._signatures),
        (root._signature_key_owner, root._signature_keys),
        (root._node_owner, root._nodes),
        (root._key_owner, root._keys),
        (root._normalization_owner, root._normalizations),
        (root._binding_owner, root._parents),
    )
    all_valid = (
        root.ledger is ledger
        and type(root._next_node) is int
        and root._next_node >= 0
        and len(root._nodes) <= root._next_node
        and len(root._keys) == len(root._nodes)
        and all(
            type(local_id) is int and 0 <= local_id < root._next_node
            for local_id in root._nodes
        )
        and all(containers.get(owner) is store for owner, store in stores)
    )
    for index, signature_record in enumerate(root._signatures):
        valid = type(signature_record) is MacroInterface
        retained: object = None
        try:
            root._validate_interface(signature_record)
            signature_handle = PortSignatureID(
                root.owner, "diamond-semantic-signature", index
            )
            valid &= root.interface(signature_handle) is signature_record
            valid &= root._signature_keys.get(signature_record) == signature_handle
            retained = root._signature_keys.get(signature_record)
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        if valid:
            approved.update((id(signature_record), id(signature_handle), id(retained)))
        else:
            invalid.add((root._signature_owner, id(signature_record)))
            all_valid = False
    for index, quotient_record in root._nodes.items():
        valid = type(quotient_record) is QuotientRecord
        try:
            valid &= type(quotient_record.components) is MacroComponents
            root._validate_components(
                quotient_record.signature, quotient_record.components
            )
            quotient_handle = LocalInterfaceID(root.owner, "diamond-quotient", index)
            valid &= root.resolve(quotient_handle) is quotient_record
            valid &= root._keys.get(quotient_record) == quotient_handle
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            valid = False
        if valid:
            approved.update(
                (
                    id(quotient_record),
                    id(quotient_record.components),
                    id(quotient_handle),
                    id(quotient_record.signature),
                )
            )
        else:
            invalid.add((root._node_owner, id(quotient_record)))
            all_valid = False
    for normalization_request, result in root._normalizations.items():
        valid = type(normalization_request) is QuotientRecord
        try:
            root._validate_components(
                normalization_request.signature, normalization_request.components
            )
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
            invalid.add((root._normalization_owner, id(normalization_request)))
            all_valid = False
    for parent_request, result in root._parents.items():
        valid = type(parent_request) is DiamondKey
        try:
            root._validate_key(parent_request)
            valid &= root.resolve(result).signature == parent_request.signature
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        if valid:
            approved.update((id(parent_request), id(result)))
        else:
            invalid.add((root._binding_owner, id(parent_request)))
            all_valid = False
    if all_valid:
        approved.update(id(store) for _, store in stores)
    return approved, invalid


__all__ = ["audit_quotient_arena"]
