"""Project Q19 owner evidence onto its exact ledger-bound payload stores."""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from typing import cast

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.q19_payload_audit import (
    audit_reverse_pair_output_roots,
    memo_payload_objects,
)


def audit_reverse_pair_output_owner(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Return only Q19 audit evidence that is a direct member of bound stores."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("Q19 payload audit requires its resource ledger")
    if type(root) is not ReversePairQ19OutputOwner:
        return PayloadAuditContribution()
    state = root.audit_snapshot()
    if state.disposed:
        return PayloadAuditContribution()
    owners = (
        *state.arena.owners,
        state.summary_owner,
        state.issued_owner,
        state.word_fibers_owner,
        state.border_certificates_owner,
        state.controlled_gt_banks_owner,
        state.spatial_bank_windows_owner,
        state.temporal_ring_banks_owner,
        state.diagonal_comparisons_owner,
        *state.projector_owners,
    )
    containers: dict[int, object] = {}
    for owner in owners:
        try:
            containers[owner] = ledger.registered_container(owner)
        except (IndexError, RuntimeError, TypeError, ValueError):
            continue
    approved_ids, _recognized, invalid_rows = audit_reverse_pair_output_roots(
        ledger, (root,), containers
    )
    bindings = (
        ("reverse_pair_output_grammar", state.arena.owners[0]),
        ("reverse_pair_output_interner", state.arena.owners[1]),
        ("reverse_pair_output_interner", state.arena.owners[2]),
        ("reverse_pair_output_interner", state.arena.owners[3]),
        ("reverse_pair_q19_summary", state.summary_owner),
        ("reverse_pair_output_occurrence", state.issued_owner),
        ("observation_memo", state.word_fibers_owner),
        ("reverse_pair_q19_border_certificate", state.border_certificates_owner),
        ("reverse_pair_q19_conditional_gt_bank", state.controlled_gt_banks_owner),
        ("reverse_pair_q19_spatial_bank_window", state.spatial_bank_windows_owner),
        ("reverse_pair_q19_temporal_ring_bank", state.temporal_ring_banks_owner),
        (
            "reverse_pair_q19_directed_diagonal_comparison",
            state.diagonal_comparisons_owner,
        ),
        *(("reverse_pair_projector_memo", owner) for owner in state.projector_owners),
    )
    if len(state.audit_bindings) != len(bindings):
        return PayloadAuditContribution(
            invalid=(PayloadAuditEntry(state.issued_owner, root),)
        )
    binding_to_snapshot: dict[int, object] = {
        4: state.summaries,
        5: state.issued,
        6: state.word_fibers,
        7: state.border_certificates,
        8: state.controlled_gt_banks,
        9: state.spatial_bank_windows,
        10: state.temporal_ring_banks,
        11: state.diagonal_comparisons,
        12: state.projector_forward,
        13: state.projector_reverse,
        14: state.projector_block,
        15: state.projector_forward_power,
        16: state.projector_reverse_power,
    }
    arena_interner_stores = state.arena.audit_interner_stores
    expected_audit_bindings = (
        state.arena.nodes,
        *arena_interner_stores,
        state.summaries.container,
        state.issued.container,
        state.word_fibers.container,
        state.border_certificates.container,
        state.controlled_gt_banks.container,
        state.spatial_bank_windows.container,
        state.temporal_ring_banks.container,
        state.diagonal_comparisons.container,
        state.projector_forward.container,
        state.projector_reverse.container,
        state.projector_block.container,
        state.projector_forward_power.container,
        state.projector_reverse_power.container,
    )
    if len(state.audit_bindings) != len(expected_audit_bindings) or any(
        actual is not expected
        for actual, expected in zip(
            state.audit_bindings, expected_audit_bindings, strict=True
        )
    ):
        return PayloadAuditContribution(
            invalid=(PayloadAuditEntry(state.issued_owner, root),)
        )
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    for index, (_role, owner) in enumerate(bindings):
        store = state.audit_bindings[index]
        if index < 4:
            if index == 0 and type(store) is LedgerList:
                members: tuple[object, ...] = tuple(cast(Iterable[object], store))
            elif isinstance(store, Mapping):
                mapping = cast(Mapping[object, object], store)
                raw_members: list[object] = []
                for raw_key in mapping:
                    key: object = raw_key
                    raw_value: object = mapping[raw_key]
                    raw_members.extend((key, raw_value))
                members = tuple(raw_members)
            else:
                invalid.append(PayloadAuditEntry(owner, store))
                continue
            approved.extend(
                PayloadAuditEntry(owner, value)
                for value in members
                if id(value) in approved_ids
            )
            invalid.extend(
                PayloadAuditEntry(owner, value)
                for value in members
                if (owner, id(value)) in invalid_rows
            )
            continue
        memo_snapshot = binding_to_snapshot.get(index)
        if type(memo_snapshot) is not OwnedMemoAuditSnapshot:
            invalid.append(PayloadAuditEntry(owner, root))
            continue
        typed_snapshot = cast(OwnedMemoAuditSnapshot[object, object], memo_snapshot)
        if typed_snapshot.container is not store:
            invalid.append(PayloadAuditEntry(owner, root))
            continue
        values = tuple(
            item for pair in memo_payload_objects(typed_snapshot) for item in pair
        )
        approved.extend(
            PayloadAuditEntry(owner, value)
            for value in values
            if id(value) in approved_ids
        )
        invalid.extend(
            PayloadAuditEntry(owner, value)
            for value in values
            if (owner, id(value)) in invalid_rows
        )
    if invalid_rows and not invalid:
        invalid.append(PayloadAuditEntry(state.issued_owner, root))
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = ["audit_reverse_pair_output_owner"]
