"""Independent admission of retained source-bound range observations.

A bounded residue or last-one witness can collectively encode a future word.
These checks inspect actual key/value relationships, independently of runtime
cache predicates and payload callbacks. Universal aligned carry cells remain a
different representation from arbitrary prefix observers.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from functools import partial
from typing import cast

from devtools.verification.collatz_carry_ranges import (
    CarryRangeSummary,
    CarryRangeTransfer,
)
from devtools.verification.lazy_collatz import (
    LazyCollatzApplication,
    LazyCollatzPayloadAuditSnapshot,
    Program,
    SummaryKey,
)
from devtools.verification.lazy_collatz_range import (
    CollatzRangeEvaluator,
    CollatzRangePayloadAuditSnapshot,
    RangeKey,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.proof_payload_admission import (
    register_proof_payload_auditor,
)


def _program(
    application: LazyCollatzPayloadAuditSnapshot,
    handle: object,
    *,
    source: bool,
) -> bool:
    if (
        type(handle) is not ActionProgramID
        or handle.owner is not application.token
        or handle.kind != "program"
        or type(handle.local_id) is not int
        or not 0 <= handle.local_id < len(application.programs)
    ):
        return False
    if source:
        return (
            handle.local_id == 0
            and application.programs[0] == Program("identity")
            and application.initial.program == handle
            and application.initial.source == application.source_ref
        )
    return True


def _summary(value: object, length: int) -> bool:
    if (
        type(value) is not CarryRangeSummary
        or type(value.length) is not int
        or value.length != length
        or type(value.exit_carry) is not int
        or not 0 <= value.exit_carry <= 2
    ):
        return False
    first, last = value.first_one, value.last_one
    return (first is None and last is None) or (
        type(first) is int and type(last) is int and 0 <= first <= last < length
    )


def _prefix(
    application: LazyCollatzPayloadAuditSnapshot,
    key: object,
    value: object,
    *,
    mul3: bool,
) -> bool:
    if (
        type(key) is not SummaryKey
        or type(key.width) is not int
        or key.width < 0
        or not _program(application, key.program, source=True)
    ):
        return False
    if not mul3:
        return (
            _summary(value, key.width)
            and isinstance(value, CarryRangeSummary)
            and value.exit_carry == 0
        )
    return (
        type(value) is CarryRangeTransfer
        and type(value.rows) is tuple
        and len(value.rows) == 3
        and all(_summary(row, key.width + 2) for row in value.rows)
    )


def _cell(
    evaluator: CollatzRangePayloadAuditSnapshot,
    key: object,
    value: object,
    *,
    event: bool,
) -> bool:
    if (
        type(key) is not RangeKey
        or type(key.start) is not int
        or type(key.length) is not int
        or key.start < 0
        or key.length < 0
        or not _program(evaluator.application, key.program, source=event)
    ):
        return False
    if event:
        return key.start == 0 and key.length > 0 and _summary(value, key.length + 2)
    if (
        key.length < 8
        or key.length & (key.length - 1)
        or key.start % key.length
        or type(value) is not TransferSummaryID
        or value.owner is not evaluator.action_owner
        or value.kind != "collatz-range-effect"
        or type(value.local_id) is not int
        or not 0 <= value.local_id < len(evaluator.effects)
    ):
        return False
    effect = evaluator.effects[value.local_id]
    return effect.length == key.length and evaluator.ids.get(effect) == value


def audit_lazy_observation_bindings(ledger: ResourceLedger) -> set[tuple[int, int]]:
    """Return owner/object identities of forbidden actual retained bindings."""
    containers: dict[int, object] = dict(ledger.iter_containers())
    roots = tuple(ledger.iter_execution_roots())
    validators: dict[int, Callable[[object, object], bool]] = {}

    def register(
        owner: int, container: object, check: Callable[[object, object], bool]
    ) -> None:
        if containers.get(owner) is container:
            validators[owner] = check

    for root in roots:
        if type(root) is LazyCollatzApplication and root.ledger is ledger:
            snapshot = root.payload_audit_snapshot()
            if (
                containers.get(snapshot.program_owner) is not snapshot.program_store
                or containers.get(snapshot.program_key_owner)
                is not snapshot.program_key_store
            ):
                continue
            register(
                snapshot.summary_owner,
                snapshot.summary_store,
                partial(_prefix, snapshot, mul3=False),
            )
            register(
                snapshot.mul3_owner,
                snapshot.mul3_store,
                partial(_prefix, snapshot, mul3=True),
            )
        elif type(root) is CollatzRangeEvaluator and root.ledger is ledger:
            range_snapshot = root.payload_audit_snapshot()
            if (
                containers.get(range_snapshot.effect_owner)
                is not range_snapshot.effect_store
                or containers.get(range_snapshot.interner_owner)
                is not range_snapshot.interner_store
            ):
                continue
            register(
                range_snapshot.ranges_owner,
                range_snapshot.ranges_store,
                partial(_cell, range_snapshot, event=False),
            )
            register(
                range_snapshot.events_owner,
                range_snapshot.events_store,
                partial(_cell, range_snapshot, event=True),
            )

    forbidden: set[tuple[int, int]] = set()
    # Walk actual stores, including nested pairs: a callback cannot erase the
    # key/result relation, and moving the pair to another role grants no scope.
    for owner, container in containers.items():
        pending: list[object] = [container]
        seen: set[int] = set()
        while pending:
            current = pending.pop()
            if id(current) in seen:
                continue
            seen.add(id(current))
            if isinstance(current, Mapping):
                mapping = cast(Mapping[object, object], current)
                pending.extend(audit_mapping_items(mapping))
            elif isinstance(current, Sequence) and not isinstance(
                current, (str, bytes)
            ):
                sequence = cast(Sequence[object], current)
                if len(sequence) == 2 and type(sequence[0]) in (SummaryKey, RangeKey):
                    key, value = sequence
                    check = validators.get(owner)
                    if check is None or not check(key, value):
                        forbidden.update(((owner, id(key)), (owner, id(value))))
                else:
                    pending.extend(sequence)
    return forbidden


register_proof_payload_auditor(audit_lazy_observation_bindings)
