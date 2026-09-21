"""Action construction and lifecycle operations for dyadic images."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnActionID,
    _ActionNode,
)
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicReturnImageWorkspace,
    )


def rollback_construction(workspace: DyadicReturnImageWorkspace) -> None:
    workspace.scheduler.dispose_source_images()
    for owner, store, nodes in (
        (workspace.action_owner, workspace.actions, 1),
        (workspace.source_owner, workspace.sources, 1),
        (workspace.support_owner, workspace.support, 1),
        (workspace.image_owner, workspace.images, 1),
        (workspace.construction_owner, workspace.construction_stack, 1),
    ):
        retained = len(store)
        store.clear()
        workspace.ledger.release(owner, entries=retained, nodes=nodes * retained)
    widths = len(workspace.by_width)
    workspace.by_width.clear()
    workspace.ledger.release(workspace.width_owner, entries=widths)
    snapshot_stores: tuple[tuple[int, LedgerDict[int, object]], ...] = (
        (workspace.action_snapshot_owner, workspace.action_snapshots),
        (workspace.source_snapshot_owner, workspace.source_snapshots),
        (workspace.support_snapshot_owner, workspace.support_snapshots),
        (workspace.image_snapshot_owner, workspace.image_snapshots),
    )
    for snapshot_owner, snapshot_store in snapshot_stores:
        snapshot_retained = len(snapshot_store)
        snapshot_store.clear()
        workspace.ledger.release(
            snapshot_owner, entries=snapshot_retained, nodes=snapshot_retained
        )
    workspace.owner = ArenaToken("dyadic-return-images-disposed")
    workspace._closed = True


def dispose(workspace: DyadicReturnImageWorkspace) -> None:
    if not workspace._closed:
        workspace._rollback_construction()


def append_action(
    workspace: DyadicReturnImageWorkspace, node: _ActionNode
) -> DyadicReturnActionID:
    workspace.ledger.reserve_many(
        (
            (workspace.action_owner, 1, 1),
            (workspace.width_owner, 1, 0),
            (workspace.action_snapshot_owner, 1, 1),
        )
    )
    identity = DyadicReturnActionID(
        workspace.owner, workspace._ACTION_KIND, len(workspace.actions)
    )
    previous = len(workspace.actions)
    try:
        workspace.actions.append(node)
        workspace.by_width[node.width] = identity
        workspace.action_snapshots[identity.local_id] = (node.width, node.children)
    except BaseException:
        workspace.by_width.pop(node.width, None)
        workspace.action_snapshots.pop(identity.local_id, None)
        workspace.actions._rollback_unpublished(previous)
        workspace.ledger.release(workspace.action_owner, entries=1, nodes=1)
        workspace.ledger.release(workspace.width_owner, entries=1)
        workspace.ledger.release(workspace.action_snapshot_owner, entries=1, nodes=1)
        raise
    workspace._bump("action_publications")
    return identity


def build_action(
    workspace: DyadicReturnImageWorkspace, width: int
) -> DyadicReturnActionID:
    found = workspace.by_width.get(width)
    if found is not None:
        return found
    if workspace.construction_stack:
        raise RuntimeError("nested dyadic return action construction")

    def push(value: int) -> None:
        workspace.ledger.reserve(workspace.construction_owner, entries=1, nodes=1)
        workspace.construction_stack.append(value)

    push(width)
    try:
        while workspace.construction_stack:
            current = workspace.construction_stack[-1]
            found = workspace.by_width.get(current)
            if found is not None:
                workspace.construction_stack.pop()
                workspace.ledger.release(
                    workspace.construction_owner, entries=1, nodes=1
                )
                continue
            if current <= workspace.MAX_LEAF_STEPS:
                workspace._append_action(_ActionNode(current, None))
                continue
            first_width = 1 << ((current - 1).bit_length() - 1)
            last_width = current - first_width
            first = workspace.by_width.get(first_width)
            last = workspace.by_width.get(last_width)
            if first is None:
                push(first_width)
                continue
            if last is None:
                push(last_width)
                continue
            workspace._append_action(_ActionNode(current, (first, last)))
            workspace._bump("action_compositions")
    finally:
        remaining = len(workspace.construction_stack)
        workspace.construction_stack.clear()
        workspace.ledger.release(
            workspace.construction_owner, entries=remaining, nodes=remaining
        )
    return workspace.by_width[width]
