"""Registration of the reverse/add output owner's exact audited stores."""

from __future__ import annotations

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding


def register_reverse_pair_output_contract(
    ledger: ResourceLedger,
    root: object,
    *,
    arena_owners: tuple[int, int, int, int],
    summary_owner: int,
    issued_owner: int,
    word_fibers_owner: int,
    border_owner: int,
    controlled_gt_owner: int,
    spatial_owner: int,
    ring_owner: int,
    diagonal_owner: int,
    projector_owners: tuple[int, int, int, int, int],
) -> None:
    """Bind each output/interner memo to its existing ledger account."""
    from number_compiler.sequences.reverse_add.q19_payload_audit_owner import (
        audit_reverse_pair_output_owner,
    )

    rows = (
        (arena_owners[0], "_audit_nodes", "reverse_pair_output_grammar"),
        (arena_owners[1], "_audit_terms", "reverse_pair_output_interner"),
        (arena_owners[2], "_audit_concats", "reverse_pair_output_interner"),
        (arena_owners[3], "_audit_repeats", "reverse_pair_output_interner"),
        (summary_owner, "_audit_summaries", "reverse_pair_q19_summary"),
        (issued_owner, "_audit_issued", "reverse_pair_output_occurrence"),
        (word_fibers_owner, "_audit_word_fibers", "observation_memo"),
        (
            border_owner,
            "_audit_border_certificates",
            "reverse_pair_q19_border_certificate",
        ),
        (
            controlled_gt_owner,
            "_audit_controlled_gt_banks",
            "reverse_pair_q19_conditional_gt_bank",
        ),
        (
            spatial_owner,
            "_audit_spatial_bank_windows",
            "reverse_pair_q19_spatial_bank_window",
        ),
        (
            ring_owner,
            "_audit_temporal_ring_banks",
            "reverse_pair_q19_temporal_ring_bank",
        ),
        (
            diagonal_owner,
            "_audit_diagonal_comparisons",
            "reverse_pair_q19_directed_diagonal_comparison",
        ),
        *(
            (owner, attribute, "reverse_pair_projector_memo")
            for owner, attribute in zip(
                projector_owners,
                (
                    "_audit_projector_forward",
                    "_audit_projector_reverse",
                    "_audit_projector_block",
                    "_audit_projector_forward_power",
                    "_audit_projector_reverse_power",
                ),
                strict=True,
            )
        ),
    )
    bindings = tuple(PayloadAuditStoreBinding(*row) for row in rows)
    ledger.register_payload_audit_contract(
        root, "reverse_add", bindings, audit_reverse_pair_output_owner
    )


__all__ = ["register_reverse_pair_output_contract"]
