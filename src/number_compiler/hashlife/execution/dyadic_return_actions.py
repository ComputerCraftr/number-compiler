"""Action construction and lifecycle operations for dyadic images."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnSupportID,
    _ActionNode,
    _ImageNode,
    _SupportNode,
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
        (workspace.macro_stack_owner, workspace.macro_stack, 1),
        (workspace.balanced_stack_owner, workspace.balanced_stack, 1),
    ):
        retained = len(store)
        store.clear()
        workspace.ledger.release(owner, entries=retained, nodes=nodes * retained)
    widths = len(workspace.by_width)
    workspace.by_width.clear()
    workspace.ledger.release(workspace.width_owner, entries=widths)
    macros = len(workspace.macros)
    workspace.macros.clear()
    workspace.ledger.release(workspace.macro_owner, entries=macros, nodes=macros)
    demanded = len(workspace.demanded_support)
    workspace.demanded_support.clear()
    workspace.ledger.release(workspace.demanded_support_owner, entries=demanded)
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
    workspace._bump("action_requests")
    found = workspace.by_width.get(width)
    if found is not None:
        workspace._bump("action_hits")
        return found
    workspace._bump("action_misses")
    if workspace.construction_stack:
        raise RuntimeError("nested dyadic return action construction")

    def push(value: int) -> None:
        previous = len(workspace.construction_stack)
        workspace.ledger.reserve(workspace.construction_owner, entries=1, nodes=1)
        try:
            workspace.construction_stack.append(value)
        except BaseException:
            workspace.construction_stack._rollback_unpublished(previous)
            workspace.ledger.release(workspace.construction_owner, entries=1, nodes=1)
            raise

    try:
        push(width)
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


def rollback_new_publications(
    self: DyadicReturnImageWorkspace, support_start: int, image_start: int
) -> None:
    """Discard an unpublished candidate's records after failed construction."""
    image_count = len(self.images) - image_start
    support_count = len(self.support) - support_start
    if image_count:
        for index in range(image_start, len(self.images)):
            self.image_snapshots.pop(index, None)
        self.images._rollback_unpublished(image_start)
        self.ledger.release(self.image_owner, entries=image_count, nodes=image_count)
        self.ledger.release(
            self.image_snapshot_owner, entries=image_count, nodes=image_count
        )
    if support_count:
        for index in range(support_start, len(self.support)):
            self.support_snapshots.pop(index, None)
        self.support._rollback_unpublished(support_start)
        self.ledger.release(
            self.support_owner, entries=support_count, nodes=support_count
        )
        self.ledger.release(
            self.support_snapshot_owner, entries=support_count, nodes=support_count
        )


def append_support(
    self: DyadicReturnImageWorkspace, node: _SupportNode
) -> DyadicReturnSupportID:
    previous = len(self.support)
    self.ledger.reserve_many(
        ((self.support_owner, 1, 1), (self.support_snapshot_owner, 1, 1))
    )
    identity = DyadicReturnSupportID(self.owner, self._SUPPORT_KIND, len(self.support))
    try:
        self.support.append(node)
        self.support_snapshots[identity.local_id] = (
            node.width,
            node.residue,
            node.transfer.upper,
            node.transfer.offset,
            node.transfer.lower,
            node.odd_steps,
            node.delta,
            node.minimum,
            node.branch_word,
            node.children,
            node.cycle,
            node.saturated,
        )
    except BaseException:
        self.support_snapshots.pop(identity.local_id, None)
        self.support._rollback_unpublished(previous)
        self.ledger.release(self.support_owner, entries=1, nodes=1)
        self.ledger.release(self.support_snapshot_owner, entries=1, nodes=1)
        raise
    return identity


def append_image(
    self: DyadicReturnImageWorkspace, node: _ImageNode
) -> DyadicReturnImageID:
    previous = len(self.images)
    self.ledger.reserve_many(
        ((self.image_owner, 1, 1), (self.image_snapshot_owner, 1, 1))
    )
    identity = DyadicReturnImageID(self.owner, self._IMAGE_KIND, len(self.images))
    try:
        self.images.append(node)
        summary = node.summary
        self.image_snapshots[identity.local_id] = (
            node.source,
            node.action,
            summary.width,
            summary.residue,
            summary.transfer.upper,
            summary.transfer.offset,
            summary.transfer.lower,
            summary.delta,
            summary.minimum,
            summary.odd_steps,
            summary.support,
            summary.cycle,
        )
    except BaseException:
        self.image_snapshots.pop(identity.local_id, None)
        self.images._rollback_unpublished(previous)
        self.ledger.release(self.image_owner, entries=1, nodes=1)
        self.ledger.release(self.image_snapshot_owner, entries=1, nodes=1)
        raise
    return identity
