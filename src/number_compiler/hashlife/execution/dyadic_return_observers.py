"""Demanded projections and read-only observers for dyadic images."""

from __future__ import annotations

from collections.abc import Iterator
from operator import add, mul
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.point_germ import AffinePointGerm
from number_compiler.arithmetic.fields.skew_transfer import (
    SkewTransfer,
    integer_dyadic_fiber_action,
)
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicCycleSummary,
    DyadicImageSummary,
    DyadicReturnImageID,
    DyadicReturnSupportID,
    _SupportNode,
)
from number_compiler.hashlife.execution.source_bound_images import SourceImageView
from number_compiler.hashlife.execution.dyadic_return_transport import (
    _low_bits,
    balanced_residue_macro,
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


def binary_cell(workspace: DyadicReturnImageWorkspace, position: int) -> int:
    """Demand one cell of the admitted image, without an endpoint or itinerary.

    The normalized germ is a spatial consumer, never successor authority.
    Reduce the affine numerator modulo the demanded precision *before*
    multiplication. The blank cutoff is pulled back by integer division.
    No source-reading DFA, alphabet enumeration or retained cursor is created.
    """
    if type(position) is not int or position < 0:
        raise ValueError("binary cell position must be a nonnegative integer")
    source = workspace.source_node(workspace.root_source)
    image = workspace.image_node(workspace.root_payload)
    action = workspace.action_node(workspace.root_action)
    if (
        image.source != workspace.root_source
        or image.action != workspace.root_action
        or action.width != workspace.steps
        or image.summary.width != workspace.steps
        or source.precision != workspace.steps
        or source.residue != _low_bits(workspace.seed, source.precision)
        or source.lift != workspace.seed >> source.precision
    ):
        raise ValueError("binary cell has another source/action binding")
    transfer = workspace.summary().transfer
    upper, offset, lower = transfer.upper, transfer.offset, transfer.lower
    workspace._bump("point_germ_demands")
    divisions = lower.bit_length() - 1
    if lower <= 0 or lower != 1 << divisions or upper < 0:
        raise ValueError("binary cell requires a nonnegative dyadic affine image")
    # Refuse no coordinates here: a remote exterior demand costs only a
    # comparison of bit lengths, rather than allocating 2**position.
    numerator_bits = (
        max(upper.bit_length() + workspace.seed.bit_length(), abs(offset).bit_length())
        + 1
    )
    if position + divisions >= numerator_bits:
        workspace._bump("point_germ_exterior_shortcuts")
        return 0 if position == 0 else 2
    place = 1 << position
    if not upper:
        value, remainder = divmod(offset, lower)
        if remainder or value < 0:
            raise ValueError("constant binary image is not nonnegative integral")
        return 2 if position and value < place else (value >> position) & 1
    shift = source.precision - divisions
    if shift < 0:
        raise ValueError("binary image has insufficient source precision")
    width = position + 1
    modulus = lower << width
    workspace._bump(
        "point_germ_operand_bits",
        upper.bit_length()
        + abs(offset).bit_length()
        + source.residue.bit_length()
        + source.lift.bit_length()
        + modulus.bit_length(),
    )
    residue = ((upper % modulus) * (source.residue % modulus) + offset) % modulus
    if residue % lower:
        raise ValueError("binary cell source has a nonintegral image")
    gain = 0 if shift >= width else (upper & ((1 << (width - shift)) - 1)) << shift
    threshold = lower * place
    first_source = -((offset - threshold) // upper)
    distance = max(0, first_source - source.residue)
    # ceil(distance / 2**precision), without constructing that power.
    cutoff = 0 if not distance else ((distance - 1) >> source.precision) + 1
    if position == 0:
        cutoff = 0  # The canonical integer zero has one zero digit.
    germ = AffinePointGerm.normal_form(width, gain, residue // lower, cutoff)
    workspace._bump("point_germ_normalizations")
    workspace._bump("point_germ_descriptor_bits", germ.descriptor_bits)
    return germ.at(source.lift)


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
        if node.saturated:
            pending.append(
                (_expanded_saturated_support(workspace, workspace.root_payload), start)
            )
            continue
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


def _expanded_saturated_support(
    workspace: DyadicReturnImageWorkspace, payload: DyadicReturnImageID
) -> DyadicReturnSupportID:
    """Demand exact bounded leaves once from the same admitted source image."""
    cached = workspace.demanded_support.get(payload)
    if cached is not None:
        workspace._bump("saturated_support_demand_hits")
        return cached
    image = workspace.image_node(payload)
    summary = image.summary
    if summary.support is None or not workspace.support_node(summary.support).saturated:
        raise ValueError("dyadic image is not a saturated publication")
    source = workspace.source_node(image.source)
    cycle = summary.cycle
    prefix = summary.width if cycle is None else cycle.entry_steps
    if not 0 < prefix <= summary.width:
        raise ValueError("saturated image has an invalid cycle boundary")
    support_start, image_start = len(workspace.support), len(workspace.images)
    try:
        prefix_id = balanced_residue_macro(
            workspace, prefix, _low_bits(source.residue, prefix)
        )
        prefix_node = workspace.support_node(prefix_id)
        if cycle is None:
            completed_id = prefix_id
        else:
            law_cycle = workspace.law.cycle
            if law_cycle is None or not source.exact:
                raise ValueError("saturated cycle requires an exact cycle law")
            source_value = workspace._source_value(source)
            numerator = (
                prefix_node.transfer.upper * source_value + prefix_node.transfer.offset
            )
            if numerator % prefix_node.transfer.lower:
                raise ArithmeticError("saturated cycle prefix was not integral")
            entry_value = numerator // prefix_node.transfer.lower
            if entry_value != law_cycle.states[cycle.cycle_phase]:
                raise ArithmeticError("saturated cycle boundary changed")
            tail_width = summary.width - prefix
            tail_cycle = DyadicCycleSummary(
                0,
                cycle.cycle_phase,
                cycle.cycles,
                cycle.remainder,
                cycle.terminal_phase,
                cycle.odd_steps,
                cycle.delta,
                cycle.minimum,
            )
            tail_id = workspace._append_support(
                _SupportNode(
                    tail_width,
                    _low_bits(entry_value, tail_width),
                    SkewTransfer(0, law_cycle.states[cycle.terminal_phase], 1),
                    cycle.odd_steps,
                    cycle.delta,
                    cycle.minimum,
                    None,
                    None,
                    tail_cycle,
                )
            )
            composed = prefix_node.transfer.then(
                workspace.support_node(tail_id).transfer, multiply=mul, add=add
            )
            completed_id = workspace._append_support(
                _SupportNode(
                    summary.width,
                    summary.residue,
                    composed,
                    prefix_node.odd_steps + cycle.odd_steps,
                    prefix_node.delta + cycle.delta,
                    min(prefix_node.minimum, prefix_node.delta + cycle.minimum),
                    None,
                    (prefix_id, tail_id),
                    cycle,
                )
            )
        completed = workspace.support_node(completed_id)
        if (
            completed.width != summary.width
            or completed.residue != summary.residue
            or completed.transfer != summary.transfer
            or completed.odd_steps != summary.odd_steps
            or completed.delta != summary.delta
            or completed.minimum != summary.minimum
            or completed.cycle != summary.cycle
        ):
            raise ArithmeticError("demanded support disagrees with admitted image")
        workspace.ledger.reserve(workspace.demanded_support_owner, entries=1)
        try:
            workspace.demanded_support[payload] = completed_id
        except BaseException:
            workspace.demanded_support.pop(payload, None)
            workspace.ledger.release(workspace.demanded_support_owner, entries=1)
            raise
        workspace._bump("saturated_support_expansions")
        return completed_id
    except BaseException:
        workspace._rollback_new_publications(support_start, image_start)
        raise


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
        if node.saturated:
            pending.append((_expanded_saturated_support(workspace, payload), start))
            continue
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
