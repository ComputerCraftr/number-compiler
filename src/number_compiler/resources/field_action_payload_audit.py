"""Owner-aware validation for retained algebraic field-action records."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit


@dataclass(frozen=True, slots=True)
class FieldActionPayloadAudit:
    approved: frozenset[int]
    invalid: frozenset[tuple[int, int]]


def audit_field_action_payloads(
    ledger: ResourceLedger,
    contracts: PayloadAuditContractAudit | None = None,
) -> FieldActionPayloadAudit:
    """Validate actual arena stores before treating their actions as semantic.

    An action class name alone grants no exemption. The owning arena, ledger,
    registered backing stores, scoped component handles, and bounded arithmetic
    invariants must all agree.
    """
    from number_compiler.resources.symbolic_innovation_payload_audit import (
        audit_symbolic_innovation_payloads,
    )

    innovations = audit_symbolic_innovation_payloads(ledger)
    if contracts is None:
        contracts = ledger.audit_payload_contracts()
    _reverse_approved, reverse_invalid = contracts.family("reverse_add", ledger=ledger)
    collatz_approved, collatz_invalid = contracts.family("collatz", ledger=ledger)
    scoped_approved = innovations.approved | frozenset(
        identity for _, identity in collatz_approved
    )
    scoped_invalid = innovations.invalid | reverse_invalid | collatz_invalid
    legacy_prefixes = (
        "number_compiler.hashlife.actions.field_actions",
        "number_compiler.hashlife.execution.field_",
        "number_compiler.sequences.reverse_add.powered_local_codec",
        "number_compiler.sequences.reverse_add.coordinate_program",
        "number_compiler.sequences.reverse_add.field_action",
    )
    if not any(
        type(root).__module__.startswith(legacy_prefixes)
        for root in ledger.iter_execution_roots()
    ):
        return FieldActionPayloadAudit(scoped_approved, scoped_invalid)

    from number_compiler.arithmetic.contracts.scoped_handles import (
        ActionProgramID,
    )
    from number_compiler.hashlife.actions.field_actions import (
        FieldCellActionID,
    )
    from number_compiler.hashlife.execution.continuations.generic_higher import (
        GenericHigherAction,
        GenericHigherActionSchema,
    )

    containers = dict(ledger.iter_containers())
    approved: set[int] = set(scoped_approved)
    invalid: set[tuple[int, int]] = set(scoped_invalid)
    for root in ledger.iter_execution_roots():
        if type(root) is GenericHigherActionSchema:
            snapshot = root.audit_snapshot()
            stores = snapshot.node_store, snapshot.key_store
            all_valid = (
                snapshot.ledger is ledger
                and root.runtime.ledger is ledger
                and (
                    containers.get(snapshot.node_owner) is snapshot.node_store
                    and containers.get(snapshot.key_owner) is snapshot.key_store
                )
            )

            def exact_action(left: object, right: object) -> bool:
                if (
                    type(left) is not ActionProgramID
                    or type(right) is not ActionProgramID
                ):
                    return False
                return (
                    left.owner is right.owner
                    and left.kind == right.kind
                    and type(left.local_id) is int
                    and type(right.local_id) is int
                    and left.local_id == right.local_id
                )

            def exact_field(left: object, right: object) -> bool:
                if (
                    type(left) is not FieldCellActionID
                    or type(right) is not FieldCellActionID
                ):
                    return False
                return (
                    left.owner is right.owner
                    and left.kind == right.kind
                    and type(left.local_id) is int
                    and type(right.local_id) is int
                    and left.local_id == right.local_id
                )

            for index, record in enumerate(snapshot.nodes):
                valid = type(record) is GenericHigherAction
                try:
                    if not valid:
                        raise TypeError("invalid generic higher record")
                    node = root.runtime.actions.resolve(record.original)
                    handle = root.handle(index)
                    valid &= root.resolve(handle) is record
                    expected = None
                    if node.kind == "compose":
                        originals = (
                            root.runtime.actions.reference(node.left),
                            root.runtime.actions.reference(node.right),
                        )
                        expected = tuple(
                            root.handle(snapshot.keys[item]) for item in originals
                        )
                    if expected is None:
                        valid &= record.children is None
                    else:
                        valid &= (
                            type(record.children) is tuple
                            and len(record.children) == 2
                            and all(
                                exact_field(actual, wanted)
                                for actual, wanted in zip(
                                    record.children, expected, strict=True
                                )
                            )
                        )
                    matches = [
                        value
                        for key, value in snapshot.keys.items()
                        if exact_action(key, record.original)
                    ]
                    valid &= (
                        len(matches) == 1
                        and type(matches[0]) is int
                        and matches[0] == index
                    )
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(record))
                else:
                    invalid.add((snapshot.node_owner, id(record)))
                    all_valid = False
            for original, index in snapshot.keys.items():
                try:
                    valid = (
                        type(original) is ActionProgramID
                        and type(index) is int
                        and 0 <= index < len(snapshot.nodes)
                    )
                    if not valid:
                        raise TypeError("invalid generic higher interner entry")
                    root.runtime.actions.resolve(original)
                    valid &= exact_action(snapshot.nodes[index].original, original)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(original), id(index)))
                else:
                    invalid.add((snapshot.key_owner, id(original)))
                    all_valid = False
            all_valid &= len(snapshot.keys) == len(snapshot.nodes)
            if all_valid:
                approved.update(id(value) for value in stores)
    return FieldActionPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["FieldActionPayloadAudit", "audit_field_action_payloads"]
