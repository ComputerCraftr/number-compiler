"""Independent inventory checks for fused-interface traversal scratch."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.tile_runtime_audit_contracts import (
    FusedTraversalWorkspaceAuditSnapshot,
)


def _valid_frame(
    adapter: PrimitiveTileKernelAdapter,
    frame: object,
    port_count: int,
) -> tuple[TileID, tuple[int, ...], bool] | None:
    if type(frame) is not tuple or len(frame) != 3:
        return None
    tile, ports, ready = frame
    if (
        type(tile) is not TileID
        or type(ports) is not tuple
        or len(ports) != port_count
        or any(type(port) is not int for port in ports)
        or type(ready) is not bool
    ):
        return None
    adapter.tiles.resolve(tile)
    return tile, ports, ready


def audit_fused_traversal_workspace(
    adapter: PrimitiveTileKernelAdapter,
    containers: Mapping[int, object],
    snapshot: FusedTraversalWorkspaceAuditSnapshot | None = None,
) -> tuple[set[int], set[tuple[int, int]]]:
    """Validate the three charged stores and every live scratch reference."""
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    workspace = (
        adapter.audit_snapshot().fused_workspace if snapshot is None else snapshot
    )
    ledger = adapter.ledger
    valid = (
        type(workspace) is FusedTraversalWorkspaceAuditSnapshot
        and type(ledger) is ResourceLedger
        and workspace.ledger is ledger
        and type(workspace.owner) is int
        and type(workspace.frame_owner) is int
        and type(workspace.value_owner) is int
        and type(workspace.active) is bool
        and type(workspace.nodes) is int
        and type(workspace.max_frames) is int
        and type(workspace.max_values) is int
        and len({workspace.owner, workspace.frame_owner, workspace.value_owner}) == 3
        and id(containers.get(workspace.owner)) == workspace.workspace_identity
        and id(containers.get(workspace.frame_owner)) == workspace.frame_store_identity
        and id(containers.get(workspace.value_owner)) == workspace.value_store_identity
    )
    try:
        accounts = ledger.inventory()
        owner_account = accounts[workspace.owner]
        frame_account = accounts[workspace.frame_owner]
        value_account = accounts[workspace.value_owner]
        valid &= (
            owner_account.role == "fused_interface_workspace"
            and frame_account.role == "fused_interface_workspace"
            and value_account.role == "fused_interface_workspace"
            and owner_account.entries == 0
            and owner_account.nodes == workspace.nodes
            and owner_account.observed_entries == 0
            and owner_account.observed_nodes == workspace.nodes
            and frame_account.entries == len(workspace.frames)
            and frame_account.nodes == 0
            and frame_account.observed_entries == len(workspace.frames)
            and frame_account.observed_nodes == 0
            and value_account.entries == len(workspace.values)
            and value_account.nodes == 0
            and value_account.observed_entries == len(workspace.values)
            and value_account.observed_nodes == 0
        )
        if workspace.active:
            valid &= (
                type(workspace.max_frames) is int
                and workspace.max_frames >= 1
                and workspace.max_frames % 2 == 1
                and type(workspace.max_values) is int
                and workspace.max_values == (workspace.max_frames + 1) // 2
                and type(workspace.nodes) is int
                and workspace.nodes > 0
                and len(workspace.frames) <= workspace.max_frames
                and len(workspace.values) <= workspace.max_values
            )
            level = (workspace.max_frames - 1) // 2
            numerator = workspace.nodes - (12 * level + 39)
            denominator = 2 * level + 5
            valid &= numerator >= 0 and numerator % denominator == 0
            port_count = numerator // denominator
        else:
            valid &= (
                workspace.nodes == 0
                and workspace.max_frames == 0
                and workspace.max_values == 0
                and not workspace.frames
                and not workspace.values
            )
            port_count = 0
        for frame in workspace.frames:
            validated = _valid_frame(adapter, frame, port_count)
            if validated is not None:
                approved.update((id(frame), id(validated[1])))
            else:
                invalid.add((workspace.frame_owner, id(frame)))
        for value in workspace.values:
            if type(value) is LocalInterfaceID:
                adapter.quotients.resolve(value)
                approved.add(id(value))
            else:
                invalid.add((workspace.value_owner, id(value)))
    except (AttributeError, KeyError, TypeError, ValueError, IndexError):
        valid = False
    if valid and not invalid:
        approved.update(
            (
                workspace.workspace_identity,
                workspace.frame_store_identity,
                workspace.value_store_identity,
            )
        )
    else:
        invalid.add((getattr(workspace, "owner", -1), workspace.workspace_identity))
    return approved, invalid


__all__ = ["audit_fused_traversal_workspace"]
