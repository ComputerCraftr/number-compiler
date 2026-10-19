"""Typed, read-only ledger views used by independent higher-payload audits."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.actions.field_actions import (
        CoordinateOutputMorphismID,
        FieldCellActionID,
    )
    from number_compiler.hashlife.execution.continuations.higher_bimachine import (
        HigherOperation,
        HigherTransfer,
    )
    from number_compiler.hashlife.execution.continuations.higher_interfaces import (
        HigherInterfaceRecord,
        HigherMacroInterface,
    )
    from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
        MacroBindingKey,
        SourceBoundHigherMacro,
    )
    from number_compiler.hashlife.execution.continuations.higher_temporal_image import (
        HigherTemporalImage,
    )
    from number_compiler.hashlife.execution.continuations.higher_types import (
        HigherExpressionID,
        HigherFunctionID,
    )
    from number_compiler.hashlife.execution.continuations.higher_values import (
        RuntimeAtom,
        RuntimeEnvironment,
        RuntimeRecord,
    )
    from number_compiler.hashlife.execution.field_images import (
        SourceBindingID,
    )
    from number_compiler.hashlife.execution.recursive_outputs import (
        RecursiveOutputRecord,
    )
    from number_compiler.hashlife.interfaces.semantic_interfaces import (
        SemanticBoundaryRecord,
    )
    from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID


@dataclass(frozen=True, slots=True)
class HigherInterfaceAuditSnapshot:
    ledger: ResourceLedger
    owner: ArenaToken
    signature_owner: int
    signatures: tuple[HigherMacroInterface, ...]
    signature_store: object
    signature_key_owner: int
    signature_keys: Mapping[HigherMacroInterface, PortSignatureID]
    signature_key_store: object
    node_owner: int
    nodes: tuple[HigherInterfaceRecord, ...]
    node_store: object
    key_owner: int
    keys: Mapping[HigherInterfaceRecord, LocalInterfaceID]
    key_store: object


@dataclass(frozen=True, slots=True)
class RecursiveOutputAuditSnapshot:
    ledger: ResourceLedger
    owner: ArenaToken
    node_owner: int
    nodes: Mapping[int, RecursiveOutputRecord]
    node_store: object
    key_owner: int
    keys: Mapping[RecursiveOutputRecord, int]
    key_store: object


@dataclass(frozen=True, slots=True)
class HigherTemporalProviderAuditSnapshot:
    ledger: ResourceLedger
    binding_owner: int
    bindings: Mapping[
        CoordinateOutputMorphismID, tuple[SourceBindingID, FieldCellActionID]
    ]
    binding_store: object


@dataclass(frozen=True, slots=True)
class HigherTemporalImageAuditSnapshot:
    ledger: ResourceLedger
    owner: ArenaToken
    node_owner: int
    nodes: tuple[HigherTemporalImage, ...]
    node_store: object
    key_owner: int
    keys: Mapping[HigherTemporalImage, int]
    key_store: object
    seal_owner: int
    seals: tuple[tuple[object, ...], ...]
    seal_store: object
    frame_owner: int
    frame_store: object
    frame_count: int
    built_owner: int
    built_store: object
    built_count: int
    source_frame_owner: int
    source_frame_store: object
    source_frame_count: int
    source_summary_owner: int
    source_summary_store: object
    source_summary_count: int
    running: bool


@dataclass(frozen=True, slots=True)
class HigherSpatialMacroAuditSnapshot:
    ledger: ResourceLedger
    binding_owner: int
    bindings: Mapping[MacroBindingKey, SourceBoundHigherMacro]
    binding_store: object


@dataclass(frozen=True, slots=True)
class RuntimeValueAuditSnapshot:
    ledger: ResourceLedger
    owner: ArenaToken
    record_owner: int
    records: Mapping[int, RuntimeRecord]
    record_store: object
    key_owner: int
    keys: Mapping[RuntimeRecord, int]
    key_store: object
    environment_owner: int
    environments: Mapping[int, RuntimeEnvironment]
    environment_store: object
    environment_key_owner: int
    environment_keys: Mapping[RuntimeEnvironment, int]
    environment_key_store: object
    memo_owner: int
    evaluations: Mapping[tuple[int, int], RuntimeAtom]
    evaluation_store: object
    operation_owner: int
    operations: Mapping[tuple[object, ...], RuntimeAtom]
    operation_store: object
    projection_owner: int
    projections: Mapping[tuple[int, int], int]
    projection_store: object
    projection_pattern_owner: int
    projection_patterns: Mapping[tuple[int, ...], int]
    projection_pattern_store: object


@dataclass(frozen=True, slots=True)
class HigherBimachineAuditSnapshot:
    ledger: ResourceLedger
    operation_owner: int
    operations: Mapping[HigherOperation, HigherExpressionID]
    operation_store: object
    transfer_owner: int
    transfers: Mapping[HigherTransfer, HigherFunctionID]
    transfer_store: object


@dataclass(frozen=True, slots=True)
class SemanticBoundaryAuditSnapshot:
    ledger: ResourceLedger
    owner: ArenaToken
    node_owner: int
    records: tuple[SemanticBoundaryRecord, ...]
    node_store: object
    key_owner: int
    keys: Mapping[SemanticBoundaryRecord, int]
    key_store: object


__all__ = [
    "HigherBimachineAuditSnapshot",
    "HigherInterfaceAuditSnapshot",
    "HigherSpatialMacroAuditSnapshot",
    "HigherTemporalProviderAuditSnapshot",
    "HigherTemporalImageAuditSnapshot",
    "RecursiveOutputAuditSnapshot",
    "RuntimeValueAuditSnapshot",
    "SemanticBoundaryAuditSnapshot",
]
