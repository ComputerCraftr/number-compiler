"""Typed, read-only contracts for the Q19 output owner."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
    from number_compiler.arithmetic.automata.slp import (
        BimachineSLPProjector,
        SLPCacheAuditView,
    )
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
    from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot
    from number_compiler.sequences.reverse_add._q19_issuance import Q19IssuanceRegistry
    from number_compiler.sequences.reverse_add.diagonal_growth_bank import (
        CertifiedDiagonalComparison,
    )
    from number_compiler.sequences.reverse_add.q19_border_control import (
        CertifiedBorderGrowth,
    )
    from number_compiler.sequences.reverse_add.q19_controlled_gt_bank import (
        SourceGuardedGTBankAction,
    )
    from number_compiler.sequences.reverse_add.q19_occurrence import (
        ReversePairOutputOccurrence,
    )
    from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
        ReverseAddSpatialBankMorphism,
    )
    from number_compiler.sequences.reverse_add.q19_word_summary import (
        FrozenPairStepLaw,
        WordSummary,
    )
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseAddTemporalRingBank,
    )
    from number_compiler.sequences.reverse_add.temporal_seed_morphism import (
        Q19WordFiber,
    )


@dataclass(frozen=True, slots=True)
class ReversePairQ19OutputAuditSnapshot:
    """Exact Q19 backing stores and lifecycle bindings for forensic audits."""

    ledger: ResourceLedger
    digits: tuple[int, ...]
    base: int
    authority: ArenaToken
    disposed: bool
    cleanup_complete: bool
    dispose_resources_complete: bool
    active_symbol_walks: int
    binding: tuple[object, ...]
    arena: LedgerSLPArena
    projector: BimachineSLPProjector
    machine: FrozenPairStepLaw
    issuance_registry: Q19IssuanceRegistry
    initial: ReversePairOutputOccurrence
    summary_owner: int
    summaries: OwnedMemoAuditSnapshot[int, WordSummary]
    issued_owner: int
    issued: OwnedMemoAuditSnapshot[tuple[int, int], ReversePairOutputOccurrence]
    word_fibers_owner: int
    word_fibers: OwnedMemoAuditSnapshot[
        tuple[int, int, int], tuple[Q19WordFiber, tuple[object, ...]]
    ]
    word_fibers_binding: OwnedMemo[
        tuple[int, int, int], tuple[Q19WordFiber, tuple[object, ...]]
    ]
    border_certificates_owner: int
    border_certificates: OwnedMemoAuditSnapshot[
        tuple[int, int, int, int], tuple[CertifiedBorderGrowth, tuple[object, ...]]
    ]
    border_certificates_binding: OwnedMemo[
        tuple[int, int, int, int], tuple[CertifiedBorderGrowth, tuple[object, ...]]
    ]
    controlled_gt_banks_owner: int
    controlled_gt_banks: OwnedMemoAuditSnapshot[
        int, tuple[SourceGuardedGTBankAction, tuple[object, ...]]
    ]
    controlled_gt_banks_binding: OwnedMemo[
        int, tuple[SourceGuardedGTBankAction, tuple[object, ...]]
    ]
    spatial_bank_windows_owner: int
    spatial_bank_windows: OwnedMemoAuditSnapshot[
        int, tuple[ReverseAddSpatialBankMorphism, tuple[object, ...]]
    ]
    spatial_bank_windows_binding: OwnedMemo[
        int, tuple[ReverseAddSpatialBankMorphism, tuple[object, ...]]
    ]
    temporal_ring_banks_owner: int
    temporal_ring_banks: OwnedMemoAuditSnapshot[
        int, tuple[ReverseAddTemporalRingBank, tuple[object, ...]]
    ]
    temporal_ring_banks_binding: OwnedMemo[
        int, tuple[ReverseAddTemporalRingBank, tuple[object, ...]]
    ]
    diagonal_comparisons_owner: int
    diagonal_comparisons: OwnedMemoAuditSnapshot[
        int, tuple[CertifiedDiagonalComparison, tuple[object, ...]]
    ]
    diagonal_comparisons_binding: OwnedMemo[
        int, tuple[CertifiedDiagonalComparison, tuple[object, ...]]
    ]
    projector_owners: tuple[int, int, int, int, int]
    projector_forward: OwnedMemoAuditSnapshot[tuple[int, int], int | None]
    projector_reverse: OwnedMemoAuditSnapshot[tuple[int, int], int | None]
    projector_block: OwnedMemoAuditSnapshot[tuple[int, int, int], int]
    projector_forward_power: OwnedMemoAuditSnapshot[tuple[int, int, int], int | None]
    projector_reverse_power: OwnedMemoAuditSnapshot[tuple[int, int, int], int | None]
    projector_cache_stores: tuple[
        SLPCacheAuditView[tuple[int, int]],
        SLPCacheAuditView[tuple[int, int]],
        SLPCacheAuditView[tuple[int, int, int]],
        SLPCacheAuditView[tuple[int, int, int]],
        SLPCacheAuditView[tuple[int, int, int]],
    ]
    audit_bindings: tuple[object, ...]


__all__ = ["ReversePairQ19OutputAuditSnapshot"]
