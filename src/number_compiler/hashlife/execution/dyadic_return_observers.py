"""Demanded projections and read-only observers for dyadic images."""

from __future__ import annotations

from collections.abc import Iterator
from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicImageSummary,
    DyadicReturnImageID,
    DyadicReturnSupportID,
    _SupportNode,
)
from number_compiler.hashlife.execution.source_bound_images import SourceImageView

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicReturnImageWorkspace,
    )


def first_failure(
    workspace: DyadicReturnImageWorkspace, image: SourceImageView
) -> int | None:
    workspace.validate_payload(image.payload)
    payload = image.payload
    if type(payload) is not DyadicReturnImageID:
        raise TypeError("dyadic return image payload has another sort")
    return workspace._first_failure(workspace.image_node(payload).summary)


def summary(workspace: DyadicReturnImageWorkspace) -> DyadicImageSummary:
    return workspace.image_node(workspace.root_payload).summary


def endpoint(workspace: DyadicReturnImageWorkspace) -> int:
    summary = workspace.summary()
    source = workspace.source_node(workspace.root_source)
    input_value = workspace._source_value(source)
    numerator = summary.transfer.upper * input_value + summary.transfer.offset
    if numerator % summary.transfer.lower:
        raise ArithmeticError("dyadic return endpoint was not integral")
    return numerator // summary.transfer.lower


def odd_steps(workspace: DyadicReturnImageWorkspace) -> int:
    return workspace.summary().odd_steps


def delta(workspace: DyadicReturnImageWorkspace) -> int:
    return workspace.summary().delta


def minimum(workspace: DyadicReturnImageWorkspace) -> int:
    return workspace.summary().minimum


def branch_segments(
    workspace: DyadicReturnImageWorkspace,
) -> Iterator[tuple[int, int, int]]:
    """Yield ``(start, width, branch_word)`` in chronological order."""
    support = workspace.summary().support
    if support is None:
        return
    pending: list[tuple[DyadicReturnSupportID, int]] = [(support, 0)]
    while pending:
        identity, start = pending.pop()
        node = workspace.support_node(identity)
        if node.branch_word is not None:
            yield start, node.width, node.branch_word
            continue
        if node.cycle is not None and node.children is None:
            yield from _cycle_branch_segments(workspace, node, start)
            continue
        if node.children is None:
            raise ValueError("dyadic return support lost its children")
        left, right = node.children
        left_node = workspace.support_node(left)
        pending.append((right, start + left_node.width))
        pending.append((left, start))


def _cycle_branch_segments(
    workspace: DyadicReturnImageWorkspace, node: _SupportNode, start: int
) -> Iterator[tuple[int, int, int]]:
    cycle = workspace.law.cycle
    metadata = node.cycle
    if cycle is None or metadata is None or metadata.entry_steps != 0:
        raise ValueError("compressed cycle support has no direct cycle origin")
    bits = tuple(state & 1 for state in cycle.states)
    if not bits:
        raise ValueError("compressed cycle support has an empty cycle")
    phase = metadata.cycle_phase
    offset = 0
    while offset < node.width:
        width = min(workspace.MAX_LEAF_STEPS, node.width - offset)
        word = 0
        for local in range(width):
            word |= bits[(phase + offset + local) % len(bits)] << local
        yield start + offset, width, word
        offset += width


def leaf_summaries(
    workspace: DyadicReturnImageWorkspace,
) -> Iterator[tuple[int, DyadicImageSummary, int]]:
    """Yield retained leaf transfers and branch words chronologically."""
    yield from workspace.leaf_summaries_for(workspace.root_payload)


def leaf_summaries_for(
    workspace: DyadicReturnImageWorkspace, payload: DyadicReturnImageID
) -> Iterator[tuple[int, DyadicImageSummary, int]]:
    """Yield bounded leaves for an already published image payload."""
    summary = workspace.image_node(payload).summary
    support = summary.support
    if support is None:
        return
    pending: list[tuple[DyadicReturnSupportID, int]] = [(support, 0)]
    while pending:
        identity, start = pending.pop()
        node = workspace.support_node(identity)
        if node.cycle is not None and node.children is None:
            continue
        if node.branch_word is not None:
            yield (
                start,
                DyadicImageSummary(
                    node.width,
                    node.residue,
                    node.transfer,
                    node.delta,
                    node.minimum,
                    node.odd_steps,
                    identity,
                ),
                node.branch_word,
            )
            continue
        if node.children is None:
            raise ValueError("dyadic return support lost its children")
        left, right = node.children
        left_node = workspace.support_node(left)
        pending.append((right, start + left_node.width))
        pending.append((left, start))


def first_failure_index(workspace: DyadicReturnImageWorkspace) -> int | None:
    """Find the first negative weighted prefix from retained support."""
    return workspace._first_failure(workspace.summary())


def _first_failure(
    workspace: DyadicReturnImageWorkspace, summary: DyadicImageSummary
) -> int | None:
    if summary.minimum >= 0:
        return None
    support = summary.support
    if support is None:
        raise ArithmeticError("failing dyadic return image has no support")
    balance = 0
    start = 0
    current = support
    while True:
        node = workspace.support_node(current)
        if node.branch_word is not None:
            for offset in range(node.width):
                bit = (node.branch_word >> offset) & 1
                balance += workspace.law.weights[bit]
                if balance < 0:
                    return start + offset
            raise ArithmeticError("dyadic return minimum lost its witness")
        if node.cycle is not None and node.children is None:
            cycle = workspace.law.cycle
            metadata = node.cycle
            if cycle is None or metadata.entry_steps != 0:
                raise ArithmeticError("singleton cycle compression lost its origin")
            bits = tuple(state & 1 for state in cycle.states)
            for offset in range(min(node.width, len(bits))):
                balance += workspace.law.weights[
                    bits[(metadata.cycle_phase + offset) % len(bits)]
                ]
                if balance < 0:
                    return start + offset
            return None
        if node.children is None:
            raise ArithmeticError("dyadic return support lost its children")
        left, right = node.children
        left_node = workspace.support_node(left)
        if balance + left_node.minimum < 0:
            current = left
            continue
        balance += left_node.delta
        start += left_node.width
        current = right
