"""Immutable observations of HashLife execution stores for independent audits."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.actions.tile_action_algebra import (
        ActionSemanticKey,
        PrimitiveTileAction,
    )
    from number_compiler.hashlife.execution.tile_application import TileApplication
    from number_compiler.hashlife.execution.tile_fused_kernel import LeafProductKey
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
    )
    from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
    from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
    from number_compiler.hashlife.tiles.tile_ports import ResultWiring
    from number_compiler.hashlife.tiles.tile_result_acquisition import (
        ResultAcquisitionLeaseOwner,
    )
    from number_compiler.hashlife.tiles.tile_result_lease_inventory import (
        BoundaryOperandLeaseInventory,
    )
    from number_compiler.hashlife.tiles.tile_result_records import (
        CompletedResult,
        FusedVariantKey,
        PoweredResultKey,
        ResultVariantKey,
    )
    from number_compiler.hashlife.tiles.tile_result_types import (
        ExecutionValue,
        MemoKey,
        ReverseKey,
        ReverseValue,
    )
    from number_compiler.hashlife.tiles.tile_results import (
        CompletedResultArena,
        ResultLease,
    )
    from number_compiler.hashlife.tiles.tiles import (
        TileAlphabet,
        TileArena,
        TileID,
        TileLease,
        TileRecord,
    )
    from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


@dataclass(frozen=True, slots=True)
class FusedTraversalWorkspaceAuditSnapshot:
    ledger: ResourceLedger
    workspace_identity: int
    owner: int
    frame_owner: int
    value_owner: int
    frame_store_identity: int
    value_store_identity: int
    frames: tuple[object, ...]
    values: tuple[object, ...]
    nodes: int
    active: bool
    disposed: bool
    max_frames: int
    max_values: int


@dataclass(frozen=True, slots=True)
class PrimitiveTileKernelAuditSnapshot:
    ledger: ResourceLedger
    owner: ArenaToken
    next_action: int
    action_owner: int
    action_store_identity: int
    actions: Mapping[int, PrimitiveTileAction]
    action_key_owner: int
    action_key_store_identity: int
    action_keys: Mapping[ActionSemanticKey, int]
    leaf_owner: int
    leaf_store_identity: int
    leaf_records: Mapping[LocalInterfaceID | LeafProductKey, int | LocalInterfaceID]
    compose_owner: int
    compose_store_identity: int
    compositions: Mapping[tuple[FieldCellActionID, FieldCellActionID], int]
    fused_workspace: FusedTraversalWorkspaceAuditSnapshot


@dataclass(frozen=True, slots=True)
class TileLeaseAuditSnapshot:
    arena: TileArena
    identity: int
    closed: bool


@dataclass(frozen=True, slots=True)
class TileArenaAuditSnapshot:
    """Read-only views of the exact stores owned by a canonical tile arena."""

    ledger: ResourceLedger
    owner: ArenaToken
    next_tile: int
    next_alphabet: int
    next_lease: int
    results: CompletedResultArena | None
    alphabet_owner: int
    alphabet_store_identity: int
    alphabets: Mapping[int, TileAlphabet]
    alphabet_key_owner: int
    alphabet_key_store_identity: int
    alphabet_keys: Mapping[TileAlphabet, int]
    node_owner: int
    node_store_identity: int
    nodes: Mapping[int, TileRecord]
    key_owner: int
    key_store_identity: int
    keys: Mapping[tuple[int, int, int, int, int], int]
    ref_owner: int
    ref_store_identity: int
    refs: Mapping[int, int]
    edge_owner: int
    edge_store_identity: int
    edges: Mapping[tuple[int, int, int], None]
    lease_owner: int
    lease_store_identity: int
    leases: Mapping[int, TileID]


@dataclass(frozen=True, slots=True)
class ResultLeaseAuditSnapshot:
    issuer: CompletedResultArena
    key: PoweredResultKey
    result: CompletedResult
    tile: TileLease
    boundary_tiles: tuple[TileLease, ...]
    operand_views: tuple[BoundaryTileView, ...]
    closed: bool


@dataclass(frozen=True, slots=True)
class TileApplicationAuditSnapshot:
    scheduler: TileScheduler
    identity: int
    action: FieldCellActionID
    ports: tuple[int, ...]
    wiring: ResultWiring
    input_lease: TileLease
    root_lease: ResultLease | None
    closed: bool


@dataclass(frozen=True, slots=True)
class LazyProjectionAuditSnapshot:
    ledger: ResourceLedger
    scheduler: TileScheduler
    application: TileApplication
    logical_extent: int
    closed: bool


@dataclass(frozen=True, slots=True)
class CompletedResultAuthorityAudit:
    action_authority: object
    validate_action: Callable[[FieldCellActionID], object]
    signature_for: Callable[[FieldCellActionID], PortSignatureID]
    validated_signature_for: Callable[[FieldCellActionID], object] | None
    validate_input: Callable[[FieldCellActionID, TileID], object] | None
    validate_output: Callable[[FieldCellActionID, TileID], object] | None
    validate_fused_action: Callable[[FieldCellActionID], object] | None
    validate_fused_wiring: (
        Callable[[FieldCellActionID, ResultWiring, ResultWiring], object] | None
    )


@dataclass(frozen=True, slots=True)
class CompletedResultArenaAuditSnapshot:
    ledger: ResourceLedger
    memo_owner: int
    memo_store_identity: int
    memo: Mapping[MemoKey, ExecutionValue]
    reverse_owner: int
    reverse_store_identity: int
    reverse: Mapping[ReverseKey, ReverseValue]
    variant_owner: int
    variant_store_identity: int
    variants: Mapping[ResultVariantKey | FusedVariantKey, int]
    tiles: TileArenaAuditSnapshot
    interfaces: DiamondQuotientArena
    action_authority: object
    validate_action: Callable[[FieldCellActionID], object]
    signature_for: Callable[[FieldCellActionID], PortSignatureID]
    validated_signature_for: Callable[[FieldCellActionID], object] | None
    validate_input: Callable[[FieldCellActionID, TileID], object] | None
    validate_output: Callable[[FieldCellActionID, TileID], object] | None
    validate_fused_action: Callable[[FieldCellActionID], object] | None
    validate_fused_wiring: (
        Callable[[FieldCellActionID, ResultWiring, ResultWiring], object] | None
    )
    boundary_lease_count: int
    operand_owner: int
    operand_store_identity: int
    operand_records: Mapping[BoundaryTileView, int]
    operand_pending_release_entries: int
    pending_ledger: ResourceLedger
    pending_tiles: TileArena
    pending_owner: int
    pending_store_identity: int
    pending_records: tuple[TileLease | int | None, ...]
    pending_clear_entries: int
    pending_clear_nodes: int
    pending_tile_reservations: int
    pending_acquisition_owner: int
    pending_acquisitions_store_identity: int

    @classmethod
    def from_stores(
        cls,
        ledger: ResourceLedger,
        memo_store: LedgerDict[MemoKey, ExecutionValue],
        reverse_store: LedgerDict[ReverseKey, ReverseValue],
        variant_store: LedgerDict[ResultVariantKey | FusedVariantKey, int],
        tiles: TileArenaAuditSnapshot,
        interfaces: DiamondQuotientArena,
        authority: CompletedResultAuthorityAudit,
        boundary_lease_count: int,
        operand_store: BoundaryOperandLeaseInventory,
        lease_acquisitions: ResultAcquisitionLeaseOwner,
        pending_acquisitions: LedgerList[TileLease | int | None],
    ) -> CompletedResultArenaAuditSnapshot:
        """Capture a result owner's stores while retaining their exact identities."""
        return cls(
            ledger=ledger,
            memo_owner=memo_store.owner,
            memo_store_identity=id(memo_store),
            memo=MappingProxyType(memo_store.backing_store),
            reverse_owner=reverse_store.owner,
            reverse_store_identity=id(reverse_store),
            reverse=MappingProxyType(reverse_store.backing_store),
            variant_owner=variant_store.owner,
            variant_store_identity=id(variant_store),
            variants=MappingProxyType(variant_store.backing_store),
            tiles=tiles,
            interfaces=interfaces,
            action_authority=authority.action_authority,
            validate_action=authority.validate_action,
            signature_for=authority.signature_for,
            validated_signature_for=authority.validated_signature_for,
            validate_input=authority.validate_input,
            validate_output=authority.validate_output,
            validate_fused_action=authority.validate_fused_action,
            validate_fused_wiring=authority.validate_fused_wiring,
            boundary_lease_count=boundary_lease_count,
            operand_owner=operand_store.owner,
            operand_store_identity=id(operand_store.records),
            operand_records=MappingProxyType(operand_store.records.backing_store),
            operand_pending_release_entries=operand_store.pending_release_entries,
            pending_ledger=lease_acquisitions.ledger,
            pending_tiles=lease_acquisitions.tiles,
            pending_owner=lease_acquisitions.owner,
            pending_store_identity=id(lease_acquisitions.records),
            pending_records=lease_acquisitions.records.snapshot(),
            pending_clear_entries=lease_acquisitions.clear_entries,
            pending_clear_nodes=lease_acquisitions.clear_nodes,
            pending_tile_reservations=lease_acquisitions.pending_tile_reservations,
            pending_acquisition_owner=pending_acquisitions.owner,
            pending_acquisitions_store_identity=id(pending_acquisitions),
        )


__all__ = [
    "FusedTraversalWorkspaceAuditSnapshot",
    "CompletedResultArenaAuditSnapshot",
    "LazyProjectionAuditSnapshot",
    "PrimitiveTileKernelAuditSnapshot",
    "ResultLeaseAuditSnapshot",
    "TileApplicationAuditSnapshot",
    "TileArenaAuditSnapshot",
    "TileLeaseAuditSnapshot",
]
