"""Independent authority validation for dyadic source-image workspaces."""

from __future__ import annotations

from collections.abc import Hashable
from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.dyadic_return_images import _low_bits
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnSourceID,
    DyadicReturnSupportID,
    _ActionNode,
    _ImageNode,
    _SourceNode,
    _SupportNode,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicReturnImageWorkspace,
    )


def action_node(
    workspace: DyadicReturnImageWorkspace, action: DyadicReturnActionID
) -> _ActionNode:
    workspace._validate_law()
    action.validate(
        workspace.owner, workspace._ACTION_KIND, size=len(workspace.actions)
    )
    node = workspace.actions[action.local_id]
    if workspace.action_snapshots.get(action.local_id) != (node.width, node.children):
        raise ValueError("dyadic return action publication was altered")
    return node


def source_node(
    workspace: DyadicReturnImageWorkspace, source: DyadicReturnSourceID
) -> _SourceNode:
    workspace._validate_law()
    source.validate(
        workspace.owner, workspace._SOURCE_KIND, size=len(workspace.sources)
    )
    node = workspace.sources[source.local_id]
    expected = (
        node.residue,
        node.precision,
        node.lift,
        node.parent,
        node.parent_action,
        node.before_image,
        node.side,
        node.exact,
    )
    if workspace.source_snapshots.get(source.local_id) != expected:
        raise ValueError("dyadic return source publication was altered")
    return node


def support_node(
    workspace: DyadicReturnImageWorkspace, support: DyadicReturnSupportID
) -> _SupportNode:
    workspace._validate_law()
    support.validate(
        workspace.owner, workspace._SUPPORT_KIND, size=len(workspace.support)
    )
    node = workspace.support[support.local_id]
    if workspace.support_snapshots.get(support.local_id) != (
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
    ):
        raise ValueError("dyadic return support publication was altered")
    return node


def image_node(
    workspace: DyadicReturnImageWorkspace, image: DyadicReturnImageID
) -> _ImageNode:
    workspace._validate_law()
    image.validate(workspace.owner, workspace._IMAGE_KIND, size=len(workspace.images))
    node = workspace.images[image.local_id]
    summary = node.summary
    if workspace.image_snapshots.get(image.local_id) != (
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
    ):
        raise ValueError("dyadic return image publication was altered")
    return node


def validate_source(workspace: DyadicReturnImageWorkspace, source: Hashable) -> None:
    workspace._validate_law()
    if workspace._closed:
        raise ValueError("disposed dyadic return image workspace")
    if type(source) is not DyadicReturnSourceID:
        raise TypeError("dyadic return images require a local source ID")
    node = workspace.source_node(source)
    if (
        type(node.residue) is not int
        or type(node.precision) is not int
        or node.precision < 0
        or node.residue < 0
        or node.residue.bit_length() > node.precision
        or type(node.lift) is not int
        or node.lift < 0
        or node.side not in (0, 1, 2)
        or type(node.exact) is not bool
    ):
        raise ValueError("invalid dyadic return source")


def validate_action(workspace: DyadicReturnImageWorkspace, action: Hashable) -> None:
    workspace._validate_law()
    if workspace._closed:
        raise ValueError("disposed dyadic return image workspace")
    if type(action) is not DyadicReturnActionID:
        raise TypeError("dyadic return images require an action ID")
    workspace.action_node(action)


def validate_payload(workspace: DyadicReturnImageWorkspace, payload: Hashable) -> None:
    workspace._validate_law()
    if type(payload) is not DyadicReturnImageID:
        raise TypeError("dyadic return images require an image ID")
    image = workspace.image_node(payload)
    source = workspace.source_node(image.source)
    action = workspace.action_node(image.action)
    summary = image.summary
    if (
        summary.width != action.width
        or summary.residue != source.residue
        or summary.minimum > min(0, summary.delta)
        or summary.minimum > 0
        or summary.odd_steps < 0
        or summary.odd_steps > summary.width
        or summary.transfer.lower <= 0
        or summary.transfer.upper < 0
        or summary.support is None
        and summary.width != 0
    ):
        raise ValueError("invalid dyadic return image")
    if summary.transfer.upper == 0 and (summary.cycle is None or not source.exact):
        raise ValueError("zero-growth dyadic image is not singleton-bound")
    if summary.cycle is not None:
        cycle = summary.cycle
        if (
            workspace.law.cycle is None
            or type(cycle.entry_steps) is not int
            or not 0 <= cycle.entry_steps <= summary.width
            or type(cycle.cycle_phase) is not int
            or not 0 <= cycle.cycle_phase < len(workspace.law.cycle.states)
            or type(cycle.cycles) is not int
            or cycle.cycles < 0
            or type(cycle.remainder) is not int
            or not 0 <= cycle.remainder < len(workspace.law.cycle.states)
            or cycle.entry_steps
            + cycle.cycles * len(workspace.law.cycle.states)
            + cycle.remainder
            != summary.width
            or cycle.odd_steps < 0
            or cycle.minimum > min(0, cycle.delta)
        ):
            raise ValueError("invalid dyadic cycle compression")
    if summary.support is not None:
        workspace.support_node(summary.support)


def validate_law(workspace: DyadicReturnImageWorkspace) -> None:
    if workspace.law.descriptor != workspace._law_snapshot:
        raise ValueError("dyadic return law publication was altered")


def validate_workspace(workspace: DyadicReturnImageWorkspace) -> None:
    """Check retained authority and root bindings without endpoint replay."""
    if workspace._closed or workspace.construction_stack:
        raise ValueError("invalid dyadic return workspace lifetime")
    workspace._validate_law()
    if workspace.by_width.get(0) != workspace.identity:
        raise ValueError("dyadic return identity was changed")
    for width, action_identity in workspace.by_width.items():
        node = workspace.action_node(action_identity)
        if node.width != width:
            raise ValueError("dyadic return action index was changed")
        if node.children is None:
            if not 0 <= width <= workspace.MAX_LEAF_STEPS:
                raise ValueError("dyadic return leaf width was changed")
        else:
            action_left, action_right = node.children
            if (
                workspace.action_node(action_left).width
                + workspace.action_node(action_right).width
                != width
            ):
                raise ValueError("dyadic return action split was changed")
    expected_residue = _low_bits(workspace.seed, workspace.steps)
    expected_lift = (
        0
        if workspace.seed.bit_length() <= workspace.steps
        else workspace.seed >> workspace.steps
    )
    if workspace.steps == 0:
        expected_residue, expected_lift = 0, workspace.seed
    if workspace.source_node(workspace.root_source) != _SourceNode(
        expected_residue, workspace.steps, expected_lift, None, None, None, 0, True
    ):
        raise ValueError("dyadic return root source was changed")
    workspace.validate_source(workspace.root_source)
    workspace.validate_action(workspace.root_action)
    workspace.validate_payload(workspace.root_payload)
    root_view = workspace.scheduler._source_image_core().view(workspace.root_image)
    if (
        root_view.binding.source != workspace.root_source
        or root_view.binding.action != workspace.root_action
        or root_view.binding.extent != workspace.steps
        or root_view.payload != workspace.root_payload
        or workspace.action_node(workspace.root_action).width != workspace.steps
        or workspace.summary().width != workspace.steps
    ):
        raise ValueError("dyadic return root image binding was changed")
    for index in range(len(workspace.images)):
        workspace.validate_payload(
            DyadicReturnImageID(workspace.owner, workspace._IMAGE_KIND, index)
        )
    for index, _raw_child in enumerate(workspace.sources):
        child_id = DyadicReturnSourceID(workspace.owner, workspace._SOURCE_KIND, index)
        child = workspace.source_node(child_id)
        if index == workspace.root_source.local_id:
            continue
        if child.parent is None or child.parent_action is None:
            raise ValueError("dyadic return child source was changed")
        parent = workspace.source_node(child.parent)
        parent_action = workspace.action_node(child.parent_action)
        if parent_action.children is None:
            raise ValueError("dyadic return child has a leaf parent")
        left_action, right_action = parent_action.children
        left_width = workspace.action_node(left_action).width
        right_width = workspace.action_node(right_action).width
        if child.side == 1:
            expected_exact = parent.exact and workspace.law.cycle is not None
            expected_lift = (
                workspace._source_value(parent) >> left_width if expected_exact else 0
            )
            if (
                child.precision != left_width
                or child.residue != _low_bits(parent.residue, left_width)
                or child.exact != expected_exact
                or child.lift != expected_lift
            ):
                raise ValueError("dyadic return first child source was changed")
        elif child.side == 2:
            if child.before_image is None or child.precision != right_width:
                raise ValueError("dyadic return second child source was changed")
            before_node = workspace.image_node(child.before_image)
            before_source = workspace.source_node(before_node.source)
            expected_exact = False
            expected_lift = 0
            expected_residue = workspace._transport_low(
                before_node.summary.transfer, parent.residue, right_width
            )
            if before_source.exact and workspace.law.cycle is not None:
                before_summary = before_node.summary
                before_value = workspace._source_value(before_source)
                numerator = (
                    before_summary.transfer.upper * before_value
                    + before_summary.transfer.offset
                )
                if numerator % before_summary.transfer.lower:
                    raise ValueError("dyadic return exact child is not integral")
                expected_value = numerator // before_summary.transfer.lower
                expected_exact = True
                expected_lift = expected_value >> right_width
                expected_residue = _low_bits(expected_value, right_width)
            if (
                child.exact != expected_exact
                or child.lift != expected_lift
                or child.residue != expected_residue
            ):
                raise ValueError("dyadic return second child exactness changed")
        else:
            raise ValueError("dyadic return child side was changed")
    for support_index, _raw_node in enumerate(workspace.support):
        support_id = DyadicReturnSupportID(
            workspace.owner, workspace._SUPPORT_KIND, support_index
        )
        current = workspace.support_node(support_id)
        if current.branch_word is not None:
            if (
                current.children is not None
                or current.width < 0
                or current.branch_word < 0
                or current.branch_word.bit_length() > current.width
            ):
                raise ValueError("dyadic return leaf support was changed")
            if current.cycle is not None:
                cycle = current.cycle
                if (
                    workspace.law.cycle is None
                    or cycle.entry_steps > current.width
                    or cycle.cycles < 0
                    or cycle.remainder < 0
                ):
                    raise ValueError("dyadic return cycle support was changed")
            if current.odd_steps < 0 or current.odd_steps > current.width:
                raise ValueError("dyadic return leaf support counts were changed")
            if current.minimum > min(0, current.delta):
                raise ValueError("dyadic return leaf support minimum was changed")
        elif current.cycle is not None and current.children is None:
            cycle = current.cycle
            if (
                workspace.law.cycle is None
                or current.transfer.upper != 0
                or cycle.entry_steps < 0
                or cycle.cycles < 0
                or cycle.remainder < 0
                or cycle.odd_steps < 0
                or cycle.minimum > min(0, cycle.delta)
            ):
                raise ValueError("dyadic return compressed support was changed")
        elif current.children is None:
            raise ValueError("dyadic return support lost its children")
        else:
            support_left, support_right = current.children
            left_node, right_node = (
                workspace.support_node(support_left),
                workspace.support_node(support_right),
            )
            if (
                support_left.local_id >= support_index
                or support_right.local_id >= support_index
                or current.width != left_node.width + right_node.width
                or current.odd_steps < 0
                or current.odd_steps > current.width
                or current.minimum > min(0, current.delta)
            ):
                raise ValueError("dyadic return composed support index was changed")
