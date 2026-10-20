"""Typed iterative-task variants for causal tile execution."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, Literal, TypeAlias, TypeVar

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
    CausalLeafInterface,
)
from number_compiler.hashlife.execution.tile_causal_results import CausalCompletedOutput
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_result_records import (
    CausalInterfaceKey,
    PoweredResultKey,
)
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.causal_types import (
    CausalMemoKey,
    CausalSpatialBuffer,
    CausalState,
)

CausalTaskOp: TypeAlias = Literal[
    "anchor",
    "advance",
    "advance_symbol",
    "emit",
    "residual",
    "output",
    "output_boundary",
    "output_chunk_list",
    "scan_chunks",
    "interface",
    "reverse_interface",
    "interface_emit",
    "child_states",
    "exact_reverse_output",
    "promote_midpoint",
    "reverse_boundary",
    "point",
    "memo_done",
    "source_root_match",
]
CausalEmptySaved: TypeAlias = tuple[()]
CausalOutputSaved: TypeAlias = (
    CausalEmptySaved
    | tuple[CausalState, CausalState]
    | tuple[CausalCompletedOutput]
    | tuple[CausalCompletedOutput, CausalState, CausalState]
)
CausalEmitSaved: TypeAlias = (
    CausalEmptySaved | tuple[CausalState, CausalState] | tuple[CausalCompletedOutput]
)
CausalResidualSaved: TypeAlias = CausalEmptySaved | tuple[CausalState]
CausalChunkBuffer: TypeAlias = CausalSpatialBuffer
CausalPortPair: TypeAlias = tuple[CausalState, CausalState]
CausalOutputBoundarySaved: TypeAlias = (
    CausalEmptySaved
    | tuple[CausalChunkBuffer, CausalState, CausalState]
    | tuple[CausalChunkBuffer]
    | tuple[CausalChunkBuffer, CausalChunkBuffer]
)
CausalInterfaceSaved: TypeAlias = (
    CausalEmptySaved
    | tuple[CausalInterfaceKey | None]
    | tuple[CausalInterfaceKey, CausalInterfacePayload]
    | tuple[CausalInterfaceKey | None, CausalInterfacePayload]
    | tuple[CausalCompletedOutput, CausalInterfaceKey | None]
    | tuple[CausalInterfaceKey | None, CausalPortPair, CausalPortPair]
    | tuple[CausalInterfaceKey | None, CausalLeafInterface]
)
CausalInterfaceEmitSaved: TypeAlias = (
    CausalEmptySaved | tuple[CausalState, CausalState] | tuple[CausalLeafInterface]
)
CausalReverseBoundarySaved: TypeAlias = (
    CausalEmptySaved
    | tuple[CausalChunkBuffer, CausalState]
    | tuple[CausalChunkBuffer, CausalChunkBuffer]
    | tuple[
        tuple[CausalChunkBuffer, CausalChunkBuffer, CausalChunkBuffer],
        int,
        None,
    ]
    | tuple[
        tuple[CausalChunkBuffer, CausalChunkBuffer, CausalChunkBuffer],
        int,
        ReverseBoundOutput | None,
    ]
)
CausalPromotionSaved: TypeAlias = (
    CausalEmptySaved | tuple[PoweredResultKey, TileID, TileID]
)
CausalPointSaved: TypeAlias = CausalEmptySaved | tuple[int]
CausalAnchorArgs: TypeAlias = tuple[FieldCellActionID, int, CausalState]
CausalAdvanceArgs: TypeAlias = tuple[
    FieldCellActionID, int, CausalState, BoundaryTileView
]
CausalAdvanceSymbolArgs: TypeAlias = tuple[FieldCellActionID, int, CausalState, int]
CausalEmitArgs: TypeAlias = tuple[FieldCellActionID, CausalState, int, CausalState]
CausalResidualArgs: TypeAlias = tuple[FieldCellActionID, int, CausalState, CausalState]
CausalOutputArgs: TypeAlias = tuple[FieldCellActionID, TileID, CausalState, CausalState]
CausalOutputBoundaryArgs: TypeAlias = tuple[
    FieldCellActionID, int, BoundaryTileView, CausalState, CausalState
]
CausalOutputChunkListArgs: TypeAlias = tuple[
    FieldCellActionID,
    CausalChunkBuffer,
    CausalChunkBuffer,
    CausalChunkBuffer,
    int,
    CausalChunkBuffer,
]
CausalScanChunksArgs: TypeAlias = tuple[
    FieldCellActionID,
    int,
    CausalChunkBuffer,
    CausalState,
    int,
    CausalChunkBuffer,
]
CausalInterfaceArgs: TypeAlias = tuple[
    FieldCellActionID, TileID, CausalState, CausalState
]
CausalInterfaceEmitArgs: TypeAlias = tuple[
    FieldCellActionID, CausalState, int, CausalState, bool
]
CausalChildStatesArgs: TypeAlias = tuple[
    FieldCellActionID, TileID, CausalState, CausalState
]
CausalExactReverseOutputArgs: TypeAlias = tuple[TileID]
CausalPromoteMidpointArgs: TypeAlias = tuple[
    FieldCellActionID, TileID, CausalState, CausalState
]
CausalReverseBoundaryArgs: TypeAlias = tuple[
    FieldCellActionID, int, BoundaryTileView, CausalState, CausalState
]
CausalPointArgs: TypeAlias = tuple[
    FieldCellActionID, TileID, int, CausalState, CausalState
]
CausalMemoDoneArgs: TypeAlias = tuple[CausalMemoKey]
CausalSourceRootMatchArgs: TypeAlias = tuple[TileID]
CausalFrameArgs: TypeAlias = (
    CausalAnchorArgs
    | CausalAdvanceArgs
    | CausalAdvanceSymbolArgs
    | CausalEmitArgs
    | CausalResidualArgs
    | CausalOutputArgs
    | CausalOutputBoundaryArgs
    | CausalOutputChunkListArgs
    | CausalScanChunksArgs
    | CausalInterfaceArgs
    | CausalInterfaceEmitArgs
    | CausalChildStatesArgs
    | CausalExactReverseOutputArgs
    | CausalPromoteMidpointArgs
    | CausalReverseBoundaryArgs
    | CausalPointArgs
    | CausalMemoDoneArgs
    | CausalSourceRootMatchArgs
)

FrameArgsT = TypeVar("FrameArgsT", bound=CausalFrameArgs)
FrameSavedT = TypeVar("FrameSavedT", bound=tuple[object, ...])


@dataclass(slots=True)
class _CausalFrame(Generic[FrameArgsT, FrameSavedT]):
    """Base storage for one operation-specific causal task frame."""

    args: FrameArgsT
    stage: int = 0
    saved: FrameSavedT | CausalEmptySaved = ()
    memoized: bool = False

    @property
    def op(self) -> CausalTaskOp:
        """Return the immutable operation identity of this frame variant."""
        raise NotImplementedError("causal frame variants define their operation")

    def payload_reference_count(self) -> int:
        """Return the direct payload slots charged by the task stack."""
        return len(self.args) + len(self.saved)


@dataclass(slots=True)
class AnchorFrame(_CausalFrame[CausalAnchorArgs, CausalEmptySaved]):
    @property
    def op(self) -> Literal["anchor"]:
        return "anchor"

    args: CausalAnchorArgs


@dataclass(slots=True)
class AdvanceFrame(_CausalFrame[CausalAdvanceArgs, CausalEmptySaved]):
    @property
    def op(self) -> Literal["advance"]:
        return "advance"

    args: CausalAdvanceArgs


@dataclass(slots=True)
class AdvanceSymbolFrame(_CausalFrame[CausalAdvanceSymbolArgs, CausalEmptySaved]):
    @property
    def op(self) -> Literal["advance_symbol"]:
        return "advance_symbol"

    args: CausalAdvanceSymbolArgs


@dataclass(slots=True)
class EmitFrame(_CausalFrame[CausalEmitArgs, CausalEmitSaved]):
    @property
    def op(self) -> Literal["emit"]:
        return "emit"

    args: CausalEmitArgs


@dataclass(slots=True)
class ResidualFrame(_CausalFrame[CausalResidualArgs, CausalResidualSaved]):
    @property
    def op(self) -> Literal["residual"]:
        return "residual"

    args: CausalResidualArgs


@dataclass(slots=True)
class OutputFrame(_CausalFrame[CausalOutputArgs, CausalOutputSaved]):
    @property
    def op(self) -> Literal["output"]:
        return "output"

    args: CausalOutputArgs


@dataclass(slots=True)
class OutputBoundaryFrame(
    _CausalFrame[CausalOutputBoundaryArgs, CausalOutputBoundarySaved]
):
    @property
    def op(self) -> Literal["output_boundary"]:
        return "output_boundary"

    args: CausalOutputBoundaryArgs

    @property
    def boundary_view(self) -> BoundaryTileView:
        """Return the boundary view carried by this task."""
        return self.args[2]


@dataclass(slots=True)
class OutputChunkListFrame(_CausalFrame[CausalOutputChunkListArgs, CausalEmptySaved]):
    @property
    def op(self) -> Literal["output_chunk_list"]:
        return "output_chunk_list"

    args: CausalOutputChunkListArgs


@dataclass(slots=True)
class ScanChunksFrame(_CausalFrame[CausalScanChunksArgs, CausalEmptySaved]):
    @property
    def op(self) -> Literal["scan_chunks"]:
        return "scan_chunks"

    args: CausalScanChunksArgs


@dataclass(slots=True)
class InterfaceFrame(_CausalFrame[CausalInterfaceArgs, CausalInterfaceSaved]):
    @property
    def op(self) -> Literal["interface"]:
        return "interface"

    args: CausalInterfaceArgs


@dataclass(slots=True)
class ReverseInterfaceFrame(_CausalFrame[CausalInterfaceArgs, CausalInterfaceSaved]):
    @property
    def op(self) -> Literal["reverse_interface"]:
        return "reverse_interface"

    args: CausalInterfaceArgs


@dataclass(slots=True)
class InterfaceEmitFrame(
    _CausalFrame[CausalInterfaceEmitArgs, CausalInterfaceEmitSaved]
):
    @property
    def op(self) -> Literal["interface_emit"]:
        return "interface_emit"

    args: CausalInterfaceEmitArgs


@dataclass(slots=True)
class ChildStatesFrame(_CausalFrame[CausalChildStatesArgs, CausalEmptySaved]):
    @property
    def op(self) -> Literal["child_states"]:
        return "child_states"

    args: CausalChildStatesArgs


@dataclass(slots=True)
class ExactReverseOutputFrame(
    _CausalFrame[CausalExactReverseOutputArgs, CausalEmptySaved]
):
    @property
    def op(self) -> Literal["exact_reverse_output"]:
        return "exact_reverse_output"

    args: CausalExactReverseOutputArgs


@dataclass(slots=True)
class PromoteMidpointFrame(
    _CausalFrame[CausalPromoteMidpointArgs, CausalPromotionSaved]
):
    @property
    def op(self) -> Literal["promote_midpoint"]:
        return "promote_midpoint"

    args: CausalPromoteMidpointArgs


@dataclass(slots=True)
class ReverseBoundaryFrame(
    _CausalFrame[CausalReverseBoundaryArgs, CausalReverseBoundarySaved]
):
    @property
    def op(self) -> Literal["reverse_boundary"]:
        return "reverse_boundary"

    args: CausalReverseBoundaryArgs


@dataclass(slots=True)
class PointFrame(_CausalFrame[CausalPointArgs, CausalPointSaved]):
    @property
    def op(self) -> Literal["point"]:
        return "point"

    args: CausalPointArgs


@dataclass(slots=True)
class MemoDoneFrame(_CausalFrame[CausalMemoDoneArgs, CausalEmptySaved]):
    @property
    def op(self) -> Literal["memo_done"]:
        return "memo_done"

    args: CausalMemoDoneArgs


@dataclass(slots=True)
class SourceRootMatchFrame(_CausalFrame[CausalSourceRootMatchArgs, CausalEmptySaved]):
    @property
    def op(self) -> Literal["source_root_match"]:
        return "source_root_match"

    args: CausalSourceRootMatchArgs


CausalTaskFrame: TypeAlias = (
    AnchorFrame
    | AdvanceFrame
    | AdvanceSymbolFrame
    | EmitFrame
    | ResidualFrame
    | OutputFrame
    | OutputBoundaryFrame
    | OutputChunkListFrame
    | ScanChunksFrame
    | InterfaceFrame
    | ReverseInterfaceFrame
    | InterfaceEmitFrame
    | ChildStatesFrame
    | ExactReverseOutputFrame
    | PromoteMidpointFrame
    | ReverseBoundaryFrame
    | PointFrame
    | MemoDoneFrame
    | SourceRootMatchFrame
)

CAUSAL_FRAME_TYPES: tuple[type[object], ...] = (
    AnchorFrame,
    AdvanceFrame,
    AdvanceSymbolFrame,
    EmitFrame,
    ResidualFrame,
    OutputFrame,
    OutputBoundaryFrame,
    OutputChunkListFrame,
    ScanChunksFrame,
    InterfaceFrame,
    ReverseInterfaceFrame,
    InterfaceEmitFrame,
    ChildStatesFrame,
    ExactReverseOutputFrame,
    PromoteMidpointFrame,
    ReverseBoundaryFrame,
    PointFrame,
    MemoDoneFrame,
    SourceRootMatchFrame,
)

__all__ = [
    "AnchorFrame",
    "AdvanceFrame",
    "AdvanceSymbolFrame",
    "CAUSAL_FRAME_TYPES",
    "ChildStatesFrame",
    "CausalTaskFrame",
    "EmitFrame",
    "ExactReverseOutputFrame",
    "InterfaceEmitFrame",
    "InterfaceFrame",
    "MemoDoneFrame",
    "OutputBoundaryFrame",
    "OutputChunkListFrame",
    "OutputFrame",
    "PointFrame",
    "PromoteMidpointFrame",
    "ResidualFrame",
    "ReverseBoundaryFrame",
    "ReverseInterfaceFrame",
    "ScanChunksFrame",
    "SourceRootMatchFrame",
]
