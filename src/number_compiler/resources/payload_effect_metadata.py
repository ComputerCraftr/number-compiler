"""Audit helpers for semantic metadata embedded in canonical effect keys."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.resources.approved_effect_keys import record_approved_effect_key
from number_compiler.resources.behavior_payload_audit import BehaviorPayloadValidator


def audit_effect_key_metadata(
    key: object,
    definition_owner: int,
    definition: object,
    *,
    behaviors: BehaviorPayloadValidator,
    approved_metadata: set[int],
    approved_key_identity_ids: set[int],
    approved_key_fingerprints: set[tuple[tuple[object, ...], ...]],
    forbidden: set[tuple[int, int]],
) -> bool:
    """Validate metadata leaves and record this effect key's safe fingerprint."""
    metadata_nodes: list[object] = [key]
    candidate_metadata: set[int] = set()
    try:
        while metadata_nodes:
            part = metadata_nodes.pop()
            if (
                type(part) not in (tuple, SemanticIdentity)
                or id(part) in approved_metadata
                or id(part) in candidate_metadata
            ):
                continue
            candidate_metadata.add(id(part))
            if is_exact_object_tuple(part):
                metadata_nodes.extend(part)
            elif type(part) is SemanticIdentity:
                behaviors.validate_identity(part)
                metadata_nodes.append(part.behavior)
    except (TypeError, ValueError, AttributeError):
        forbidden.add((definition_owner, id(definition)))
        return False
    record_approved_effect_key(
        key,
        authorized_identity_ids=approved_key_identity_ids,
        approved_fingerprints=approved_key_fingerprints,
    )
    approved_metadata.update(candidate_metadata)
    return True


__all__ = ["audit_effect_key_metadata"]
