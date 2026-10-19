"""Typed borrowed-store views used only during explicit field-image audits."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile
    from number_compiler.arithmetic.fields.radial_innovation import (
        InnovationID,
        InnovationNode,
    )
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.actions.field_actions import (
        FieldCellActionID,
        FieldGeometryID,
    )
    from number_compiler.hashlife.execution.continuations.concrete_port_records import (
        ComposedPort,
        PortAtom,
        Residual,
        VirtualBinding,
        VirtualInterface,
        VirtualInterfaceID,
    )
    from number_compiler.hashlife.execution.continuations.provider_absorption import (
        ProviderAction,
        ProviderBindingKey,
        ProviderPointKey,
    )
    from number_compiler.hashlife.execution.continuations.provider_fused_transfer import (
        FusedProviderBinding,
        ProviderFusedPointKey,
        ProviderFusedWidthKey,
    )
    from number_compiler.hashlife.execution.continuations.provider_image_input import (
        ProviderImageInput,
        ProviderImageInputID,
    )
    from number_compiler.hashlife.execution.continuations.provider_layers import (
        ProviderLayerNode,
    )
    from number_compiler.hashlife.execution.field_image_domains import (
        FieldImageDomainEntry,
        FieldImageDomainKey,
    )
    from number_compiler.hashlife.execution.field_images import (
        FieldImageID,
        FieldImageRecord,
        FieldImageSemanticKey,
        ImageRequestKey,
        SourceBindingID,
        SourceCellRecord,
        SourceForestRecord,
    )
    from number_compiler.hashlife.execution.field_transfers import (
        FieldTransferID,
        FieldTransferKey,
        FieldTransferRecord,
        FieldTransferRequestKey,
    )
    from number_compiler.hashlife.execution.source_image_seals import TypedPayloadKey
    from number_compiler.hashlife.interfaces.semantic_structures import (
        DiamondKey,
        DiamondQuotientID,
        MacroInterface,
        QuotientRecord,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.resources.owned_memo import OwnedMemo


@dataclass(frozen=True, slots=True)
class SourceCellArenaAuditSnapshot:
    """Read-only references to the exact source stores used by an audit."""

    ledger: ResourceLedger
    owner: ArenaToken
    cell_kind: str
    node_owner: int
    nodes: Sequence[SourceCellRecord]
    key_owner: int
    keys: Mapping[DyadicTile, int]
    forest_kind: str
    forest_node_owner: int
    forests: Sequence[SourceForestRecord]
    forest_key_owner: int
    forest_keys: Mapping[tuple[tuple[int, ...], int], int]


@dataclass(frozen=True, slots=True)
class RecursiveFieldImageAuditSnapshot:
    """Read-only references to exact image stores for an explicit audit."""

    ledger: ResourceLedger
    owner: ArenaToken
    image_kind: str
    next_id: int
    domain_owner: int
    domains: Mapping[FieldImageDomainKey, FieldImageDomainEntry]
    node_owner: int
    nodes: Mapping[int, FieldImageRecord]
    key_owner: int
    keys: Mapping[FieldImageSemanticKey, int]
    binding_owner: int
    bindings: Mapping[ImageRequestKey, FieldImageID]


@dataclass(frozen=True, slots=True)
class ProviderAbsorptionAuditSnapshot:
    """Exact read-only stores retained by one provider absorption arena."""

    ledger: ResourceLedger
    owner: ArenaToken
    action_kind: str
    next_id: int
    node_owner: int
    nodes: Mapping[int, ProviderAction]
    key_owner: int
    keys: Mapping[ProviderAction, int]
    binding_owner: int
    bindings: Mapping[ProviderBindingKey, None]
    point_owner: int
    points: Mapping[ProviderPointKey, int]


@dataclass(frozen=True, slots=True)
class ProviderFusedTransferAuditSnapshot:
    """Exact read-only stores retained by one fused provider transfer."""

    ledger: ResourceLedger
    binding_owner: int
    bindings: Mapping[FusedProviderBinding, None]
    point_owner: int
    points: Mapping[ProviderFusedPointKey, int]
    width_owner: int
    widths: Mapping[ProviderFusedWidthKey, int]


@dataclass(frozen=True, slots=True)
class DiamondQuotientAuditSnapshot:
    """Exact read-only stores retained by a diamond quotient arena."""

    ledger: ResourceLedger
    owner: ArenaToken
    next_node: int
    signature_owner: int
    signatures: Sequence[MacroInterface]
    signature_key_owner: int
    signature_keys: Mapping[MacroInterface, PortSignatureID]
    node_owner: int
    nodes: Mapping[int, QuotientRecord]
    key_owner: int
    keys: Mapping[QuotientRecord, DiamondQuotientID]
    normalization_owner: int
    normalizations: Mapping[QuotientRecord, DiamondQuotientID]
    binding_owner: int
    parents: Mapping[DiamondKey, DiamondQuotientID]


@dataclass(frozen=True, slots=True)
class FieldTransferAuditSnapshot:
    """Exact read-only stores retained by a field transfer arena."""

    ledger: ResourceLedger
    owner: ArenaToken
    transfer_kind: str
    next_id: int
    node_owner: int
    nodes: Mapping[int, FieldTransferRecord]
    key_owner: int
    keys: Mapping[FieldTransferKey, int]
    binding_owner: int
    bindings: Mapping[FieldTransferRequestKey, FieldTransferID]
    observation_owner: int
    observation_bindings: Mapping[tuple[FieldTransferID, SourceBindingID], None]


@dataclass(frozen=True, slots=True)
class SymbolicInnovationAuditSnapshot:
    """Typed view of the exact stores and optional memo owned by an arena."""

    ledger: ResourceLedger
    owner: ArenaToken
    closed: bool
    node_owner: int
    nodes: Sequence[InnovationNode]
    key_owner: int
    keys: Mapping[InnovationNode, InnovationID]
    projection: OwnedMemo[InnovationID, tuple[int, ...]]
    f5_composition_owner: int | None
    f5_compositions: (
        OwnedMemo[tuple[InnovationID, InnovationID, int, int], InnovationID] | None
    )


@dataclass(frozen=True, slots=True)
class ProviderLayerArenaAuditSnapshot:
    """Exact read-only stores retained by a concrete provider-layer arena."""

    ledger: ResourceLedger
    owner: ArenaToken
    kind: str
    next_id: int
    node_owner: int
    nodes: Mapping[int, ProviderLayerNode]
    key_owner: int
    keys: Mapping[ProviderLayerNode, int]


@dataclass(frozen=True, slots=True)
class ConcretePortSchedulerAuditSnapshot:
    """Exact read-only stores retained by a concrete-port scheduler."""

    ledger: ResourceLedger
    owner: ArenaToken
    port_kind: str
    residual_kind: str
    virtual_kind: str
    next_port: int
    next_residual: int
    next_virtual: int
    port_owner: int
    ports: Mapping[int, ComposedPort]
    port_key_owner: int
    port_keys: Mapping[ComposedPort, int]
    residual_owner: int
    residuals: Mapping[int, Residual]
    residual_key_owner: int
    residual_keys: Mapping[Residual, int]
    memo_owner: int
    memo: Mapping[tuple[object, ...], PortAtom]
    virtual_owner: int
    virtual: Mapping[int, VirtualInterface]
    virtual_key_owner: int
    virtual_keys: Mapping[VirtualInterface, int]
    virtual_binding_owner: int
    virtual_bindings: Mapping[VirtualBinding, VirtualInterfaceID]
    layers: ProviderLayerArenaAuditSnapshot


@dataclass(frozen=True, slots=True)
class ProviderImageInputAuditSnapshot:
    """Exact read-only stores retained by a provider-image input arena."""

    ledger: ResourceLedger
    owner: ArenaToken
    kind: str
    next_id: int
    node_owner: int
    nodes: Mapping[int, ProviderImageInput]
    key_owner: int
    keys: Mapping[tuple[ProviderBindingKey, ImageRequestKey, int], int]
    child_owner: int
    children: Mapping[
        tuple[
            int,
            FieldCellActionID | None,
            FieldGeometryID | None,
            TypedPayloadKey,
        ],
        tuple[ProviderImageInputID, ProviderImageInputID],
    ]


__all__ = [
    "ProviderAbsorptionAuditSnapshot",
    "ProviderFusedTransferAuditSnapshot",
    "DiamondQuotientAuditSnapshot",
    "FieldTransferAuditSnapshot",
    "ConcretePortSchedulerAuditSnapshot",
    "ProviderLayerArenaAuditSnapshot",
    "ProviderImageInputAuditSnapshot",
    "RecursiveFieldImageAuditSnapshot",
    "SourceCellArenaAuditSnapshot",
]
