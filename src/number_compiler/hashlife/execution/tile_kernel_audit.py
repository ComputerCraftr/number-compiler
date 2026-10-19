"""Immutable tile-kernel audit snapshot construction."""

from __future__ import annotations

from collections.abc import Mapping
from types import MappingProxyType

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.tile_action_algebra import (
    ActionSemanticKey,
    PrimitiveTileAction,
)
from number_compiler.hashlife.execution.tile_fused_kernel import LeafProductKey
from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict
from number_compiler.resources.tile_runtime_audit_contracts import (
    FusedTraversalWorkspaceAuditSnapshot,
    PrimitiveTileKernelAuditSnapshot,
)


def tile_kernel_audit_snapshot(
    *,
    ledger: ResourceLedger,
    owner: ArenaToken,
    next_action: int,
    action_owner: int,
    actions: Mapping[int, PrimitiveTileAction],
    action_keys_owner: int,
    action_keys: Mapping[ActionSemanticKey, int],
    leaf_owner: int,
    leaf_records: Mapping[LocalInterfaceID | LeafProductKey, int | LocalInterfaceID],
    compose_owner: int,
    compositions: Mapping[tuple[FieldCellActionID, FieldCellActionID], int],
    fused_workspace: FusedTraversalWorkspaceAuditSnapshot,
    action_store: LedgerDict[int, PrimitiveTileAction],
    action_key_store: LedgerDict[ActionSemanticKey, int],
    leaf_store: LedgerDict[LocalInterfaceID | LeafProductKey, int | LocalInterfaceID],
    compose_store: LedgerDict[tuple[FieldCellActionID, FieldCellActionID], int],
) -> PrimitiveTileKernelAuditSnapshot:
    """Build detached row maps while preserving exact backing-store identities."""
    return PrimitiveTileKernelAuditSnapshot(
        ledger=ledger,
        owner=owner,
        next_action=next_action,
        action_owner=action_owner,
        action_store_identity=id(action_store),
        actions=MappingProxyType(dict(actions)),
        action_key_owner=action_keys_owner,
        action_key_store_identity=id(action_key_store),
        action_keys=MappingProxyType(dict(action_keys)),
        leaf_owner=leaf_owner,
        leaf_store_identity=id(leaf_store),
        leaf_records=MappingProxyType(dict(leaf_records)),
        compose_owner=compose_owner,
        compose_store_identity=id(compose_store),
        compositions=MappingProxyType(dict(compositions)),
        fused_workspace=fused_workspace,
    )


__all__ = ["tile_kernel_audit_snapshot"]
