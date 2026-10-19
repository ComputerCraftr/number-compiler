"""Typed snapshots consumed by the causal resource inventory audit."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Generic, TypeVar

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.resources.causal_types import (
    CausalMemoKey,
    CausalSpatialValue,
    CausalTaskValue,
)
from number_compiler.resources.stores import LedgerDict, LedgerList

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.causal_frames import CausalTaskFrame
    from number_compiler.hashlife.execution.tile_directed_transfer import (
        DirectedTransferFrame,
    )
    from number_compiler.hashlife.tiles.reverse_threshold_summary import (
        ReverseThresholdFrame,
    )
    from number_compiler.resources.causal_workspace import (
        CausalActionAdmission,
        CausalTaskWorkspace,
        SpatialReferenceBuffer,
    )

SpatialValueT = TypeVar("SpatialValueT", bound=CausalSpatialValue)
StackValueT = TypeVar("StackValueT")


@dataclass(frozen=True, slots=True)
class CausalStackAuditSnapshot(Generic[StackValueT]):
    """Typed inspection of retained stack values and their ledger wrapper."""

    owner: int
    store: LedgerList[StackValueT]
    values: tuple[StackValueT, ...]
    payload_references: int | None


@dataclass(frozen=True, slots=True)
class CausalSpatialWorkspaceAuditSnapshot(Generic[SpatialValueT]):
    """Detached entries plus the exact registered stores backing a workspace."""

    owner: int
    buffer_owner: int
    slots: int
    object_bytes: int
    next_identity: int
    buffers: tuple[tuple[int, SpatialReferenceBuffer[SpatialValueT]], ...]
    references: tuple[tuple[tuple[int, int], SpatialValueT | None], ...]
    reference_store: LedgerDict[tuple[int, int], SpatialValueT | None]
    buffer_store: LedgerDict[int, SpatialReferenceBuffer[SpatialValueT]]


@dataclass(frozen=True, slots=True)
class CausalTaskWorkspaceAuditSnapshot:
    """Typed, read-only publication snapshot for the causal resource audit."""

    workspace: CausalTaskWorkspace
    memo_owner: int
    active_owner: int
    action_pending_owner: int
    action_admitted_owner: int
    memo_store: LedgerDict[CausalMemoKey, CausalTaskValue]
    active_store: LedgerDict[CausalMemoKey, bool]
    pending_store: LedgerList[FieldCellActionID]
    admitted_store: LedgerDict[FieldCellActionID, tuple[object, ...]]
    memo_items: tuple[tuple[CausalMemoKey, CausalTaskValue], ...]
    active_items: tuple[tuple[CausalMemoKey, bool], ...]
    pending_actions: tuple[FieldCellActionID, ...]
    admitted_items: tuple[tuple[FieldCellActionID, tuple[object, ...]], ...]
    action_admission: CausalActionAdmission | None
    issued_action_admission: CausalActionAdmission | None
    run_token: object | None
    admission_closing: bool
    frames: CausalStackAuditSnapshot[CausalTaskFrame]
    summary_frames: CausalStackAuditSnapshot[ReverseThresholdFrame]
    values: CausalStackAuditSnapshot[CausalTaskValue]
    directed_frames: CausalStackAuditSnapshot[DirectedTransferFrame]
    directed_values: CausalStackAuditSnapshot[int]


__all__ = [
    "CausalSpatialWorkspaceAuditSnapshot",
    "CausalStackAuditSnapshot",
    "CausalTaskWorkspaceAuditSnapshot",
]
