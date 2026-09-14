"""Closed type unions for the shared tile result and reverse-index stores."""

from __future__ import annotations

from typing import TypeAlias, TypeGuard

from number_compiler.arithmetic.formula.summary import BlockSummary
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.tiles.tile_result_records import (
    BehaviorBindingKey,
    BoundaryConcatKey,
    BoundaryConcatResult,
    CausalInterfaceKey,
    CompletedBehaviorClassification,
    CompletedInterfaceResult,
    CompletedResult,
    DirectedTransferKey,
    FusedInterfaceKey,
    NormalizedRegionKey,
    NormalizedRegionResult,
    PoweredInterfaceKey,
    PoweredResultKey,
    ReverseBoundOutputKey,
    ReverseThresholdSummaryKey,
    RootMatchResult,
    SourceRootMatchKey,
    SpatialInterfaceKey,
    _ReverseHead,
    _ReverseLinks,
    _ReverseMember,
)

ReverseKey: TypeAlias = _ReverseHead | _ReverseMember
ExecutionKey: TypeAlias = (
    PoweredResultKey
    | PoweredInterfaceKey
    | FusedInterfaceKey
    | CausalInterfaceKey
    | DirectedTransferKey
    | ReverseThresholdSummaryKey
    | ReverseBoundOutputKey
    | SourceRootMatchKey
    | BehaviorBindingKey
    | NormalizedRegionKey
    | BoundaryConcatKey
)
MemoKey: TypeAlias = ExecutionKey | SpatialInterfaceKey
ExecutionValue: TypeAlias = (
    CompletedResult
    | CompletedInterfaceResult
    | CompletedBehaviorClassification
    | NormalizedRegionResult
    | BoundaryConcatResult
    | LocalInterfaceID
    | int
    | BlockSummary
    | ReverseBoundOutput
    | RootMatchResult
)
ReverseValue: TypeAlias = ExecutionKey | _ReverseLinks


def is_execution_key(value: object) -> TypeGuard[ExecutionKey]:
    return type(value) in (
        PoweredResultKey,
        PoweredInterfaceKey,
        FusedInterfaceKey,
        CausalInterfaceKey,
        DirectedTransferKey,
        ReverseThresholdSummaryKey,
        ReverseBoundOutputKey,
        SourceRootMatchKey,
        BehaviorBindingKey,
        NormalizedRegionKey,
        BoundaryConcatKey,
    )


__all__ = [
    "ExecutionKey",
    "ExecutionValue",
    "MemoKey",
    "ReverseKey",
    "ReverseValue",
    "is_execution_key",
]
