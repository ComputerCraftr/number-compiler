"""Demanded projections and read-only observers for dyadic images."""

from __future__ import annotations

from collections.abc import Iterator
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.skew_transfer import integer_dyadic_fiber_action
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicImageSummary,
    DyadicReturnImageID,
    DyadicReturnSupportID,
    _SupportNode,
)
from number_compiler.hashlife.execution.source_bound_images import SourceImageView
from number_compiler.hashlife.execution.dyadic_return_transport import (
    cycle_phase_summaries,
)

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
    summary = workspace.saturated_summary()
    source = workspace.source_node(workspace.root_source)
    chart = integer_dyadic_fiber_action(
        summary.transfer, source.residue, source.precision
    )
    workspace._bump("fiber_endpoint_demands")
    workspace._bump(
        "fiber_endpoint_operand_bits",
        max(1, abs(chart.multiplier).bit_length())
        + max(1, abs(chart.addend).bit_length())
        + max(1, source.lift.bit_length()),
    )
    return chart.addend + chart.multiplier * source.lift


def odd_steps(workspace: DyadicReturnImageWorkspace) -> int:
    return workspace.saturated_summary().odd_steps


def delta(workspace: DyadicReturnImageWorkspace) -> int:
    return workspace.saturated_summary().delta


def minimum(workspace: DyadicReturnImageWorkspace) -> int:
    return workspace.saturated_summary().minimum


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
            safety, _cycle_odd, _remainder_safety, _remainder_odd = (
                cycle_phase_summaries(
                    workspace.law, metadata.cycle_phase, metadata.remainder
                )
            )
            failing_copy = safety.first_failing_copy(balance, metadata.cycles)
            copies = metadata.cycles if failing_copy is None else failing_copy
            cycle_length = len(cycle.states)
            offset = copies * cycle_length
            balance += copies * safety.delta
            limit = metadata.remainder if failing_copy is None else cycle_length
            workspace._bump("cycle_safety_descent_demands")
            for local in range(limit):
                state = cycle.states[(metadata.cycle_phase + local) % cycle_length]
                balance += workspace.law.weights[state & 1]
                if balance < 0:
                    return start + offset + local
            raise ArithmeticError("failing cycle summary lost its first failure")
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
