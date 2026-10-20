"""Independent retained-payload admission for shared associated actions."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import TypeGuard

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.fields.consumer_pullback import (
    ZERO,
    AssociatedActionArena,
    AssociatedActionArenaAuditSnapshot,
    AssociatedActionID,
    AssociatedActionRecord,
    ExactRational,
    SaturatingAffineAction,
    ThresholdDemand,
)
from number_compiler.hashlife.execution.associated_action_images import (
    AssociatedScalarPayload,
    AssociatedScalarSource,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class AssociatedActionPayloadAudit:
    arenas: Mapping[ArenaToken, AssociatedActionArena]
    approved: frozenset[int]
    recognized: frozenset[int]
    invalid: frozenset[tuple[int, int]]

    def recognizes(self, value: object) -> bool:
        return (
            type(value)
            in (
                ExactRational,
                ThresholdDemand,
                SaturatingAffineAction,
                AssociatedActionID,
                AssociatedActionRecord,
                AssociatedScalarSource,
                AssociatedScalarPayload,
            )
            or id(value) in self.recognized
        )

    def valid(self, value: object) -> bool:
        if type(value) is ExactRational:
            try:
                value.validate()
            except (TypeError, ValueError, AttributeError):
                return False
            return True
        if type(value) is ThresholdDemand:
            try:
                value.__post_init__()
            except (TypeError, ValueError, AttributeError):
                return False
            return True
        if type(value) is SaturatingAffineAction:
            try:
                value.__post_init__()
            except (TypeError, ValueError, AttributeError):
                return False
            return True
        if type(value) is AssociatedScalarSource:
            try:
                value.__post_init__()
            except (TypeError, ValueError, AttributeError):
                return False
            return True
        if type(value) is AssociatedScalarPayload:
            try:
                value.__post_init__()
            except (TypeError, ValueError, AttributeError):
                return False
            return True
        if type(value) is AssociatedActionID:
            arena = self.arenas.get(value.owner)
            if arena is None:
                return False
            try:
                arena.record(value)
            except (TypeError, ValueError, IndexError, AttributeError):
                return False
            return True
        return id(value) in self.approved


def audit_associated_action_payloads(
    ledger: ResourceLedger,
    execution_roots: tuple[object, ...],
    actual_containers: Mapping[int, object],
) -> AssociatedActionPayloadAudit:
    """Validate arena provenance, interners, chronology, and scalar packets."""
    arenas: dict[ArenaToken, AssociatedActionArena] = {}
    snapshots: dict[ArenaToken, AssociatedActionArenaAuditSnapshot] = {}
    for root in execution_roots:
        if type(root) is not AssociatedActionArena or root.ledger is not ledger:
            continue
        snapshot = root.audit_snapshot()
        if snapshot.ledger is ledger and not snapshot.closed:
            arenas[snapshot.owner] = root
            snapshots[snapshot.owner] = snapshot
    approved: set[int] = set()
    recognized: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for owner, arena in arenas.items():
        snapshot = snapshots[owner]
        stores = (
            (snapshot.semantic_owner, snapshot.semantic_store_identity),
            (snapshot.semantic_key_owner, snapshot.semantic_key_store_identity),
            (
                snapshot.semantic_fingerprint_owner,
                snapshot.semantic_fingerprint_store_identity,
            ),
            (snapshot.action_owner, snapshot.action_store_identity),
            (snapshot.action_key_owner, snapshot.action_key_store_identity),
            (
                snapshot.action_fingerprint_owner,
                snapshot.action_fingerprint_store_identity,
            ),
        )
        if any(
            actual_containers.get(store_owner) is None
            or id(actual_containers[store_owner]) != identity
            for store_owner, identity in stores
        ):
            invalid.add((snapshot.action_owner, id(arena)))
            continue
        for semantic_index, semantic_value in enumerate(snapshot.semantics):
            recognized.add(id(semantic_value))
            try:
                if type(semantic_value) is not SaturatingAffineAction:
                    raise TypeError("associated arena contains another semantic sort")
                semantic_value.__post_init__()
                fingerprint = snapshot.semantic_fingerprints[semantic_index]
                recognized.add(id(fingerprint))
                if fingerprint != arena.semantic_fingerprint(semantic_value):
                    raise ValueError("associated semantic fingerprint is inconsistent")
                if arena.semantic_key_index(semantic_value) != semantic_index:
                    raise ValueError("associated semantic interner is inconsistent")
            except (TypeError, ValueError, AttributeError):
                invalid.add((snapshot.semantic_owner, id(semantic_value)))
            else:
                approved.update((id(semantic_value), id(fingerprint)))
        for semantic_key, stored_semantic_index in snapshot.semantic_key_rows:
            recognized.add(id(semantic_key))
            if (
                type(semantic_key) is not SaturatingAffineAction
                or type(stored_semantic_index) is not int
                or not 0 <= stored_semantic_index < len(snapshot.semantics)
                or snapshot.semantics[stored_semantic_index] != semantic_key
            ):
                invalid.add((snapshot.semantic_key_owner, id(semantic_key)))
        for local_id, action_value in enumerate(snapshot.actions):
            recognized.add(id(action_value))
            action_key: (
                tuple[
                    int,
                    int,
                    tuple[AssociatedActionID, AssociatedActionID] | None,
                ]
                | None
            ) = None
            try:
                if type(action_value) is not AssociatedActionRecord:
                    raise TypeError("associated arena contains another action sort")
                if (
                    type(action_value.semantic_id) is not int
                    or not 0 <= action_value.semantic_id < len(snapshot.semantics)
                    or type(action_value.logical_extent) is not int
                    or action_value.logical_extent < 0
                    or type(action_value.zero_failure_absorbing) is not bool
                ):
                    raise ValueError("associated action record has invalid metadata")
                action_id = arena.scoped_handle(local_id)
                fingerprint = snapshot.action_fingerprints[local_id]
                recognized.add(id(fingerprint))
                if fingerprint != arena.action_fingerprint(action_value):
                    raise ValueError("associated action fingerprint is inconsistent")
                semantic_value = arena.semantic(action_id)
                children = action_value.children
                if children is None:
                    applied_zero = semantic_value.apply(ZERO)
                    absorbs = applied_zero is not None and applied_zero <= ZERO
                else:
                    if type(children) is not tuple or len(children) != 2:
                        raise TypeError("associated action children are malformed")
                    before, after = children
                    before_record = arena.record(before)
                    after_record = arena.record(after)
                    if (
                        semantic_value
                        != arena.semantic(before).then(arena.semantic(after))
                        or action_value.logical_extent
                        != before_record.logical_extent + after_record.logical_extent
                    ):
                        raise ValueError("associated composition is inconsistent")
                    absorbs = (
                        before_record.zero_failure_absorbing
                        and after_record.zero_failure_absorbing
                    )
                if action_value.zero_failure_absorbing != absorbs:
                    raise ValueError("associated recovery certificate is invalid")
                action_key = (
                    action_value.semantic_id,
                    action_value.logical_extent,
                    children,
                )
                if arena.action_key_index(action_key) != local_id:
                    raise ValueError("associated action interner is inconsistent")
            except (TypeError, ValueError, IndexError, AttributeError):
                invalid.add((snapshot.action_owner, id(action_value)))
            else:
                assert action_key is not None
                approved.update((id(action_value), id(action_key), id(fingerprint)))
                recognized.update((id(action_key), id(fingerprint)))
        for stored_key, stored_id in snapshot.action_key_rows:
            recognized.add(id(stored_key))
            if (
                not _is_three_item_key(stored_key)
                or type(stored_id) is not int
                or not 0 <= stored_id < len(snapshot.actions)
            ):
                invalid.add((snapshot.action_key_owner, id(stored_key)))
                continue
            action_value = snapshot.actions[stored_id]
            if stored_key != (
                action_value.semantic_id,
                action_value.logical_extent,
                action_value.children,
            ):
                invalid.add((snapshot.action_key_owner, id(stored_key)))
            else:
                approved.add(id(stored_key))
    return AssociatedActionPayloadAudit(
        arenas,
        frozenset(approved),
        frozenset(recognized),
        frozenset(invalid),
    )


__all__ = ["AssociatedActionPayloadAudit", "audit_associated_action_payloads"]


def _is_three_item_key(
    value: object,
) -> TypeGuard[tuple[object, object, object]]:
    return is_exact_object_tuple(value) and len(value) == 3
