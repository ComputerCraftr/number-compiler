"""Publish exact dyadic cylinders from an admitted Collatz boundary word.

The four boundary families have compact run or period-two grammars.  This
module slices those grammars algebraically, so a long admitted macro can seed
the existing dyadic source cache without replaying its normalized symbols.
"""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.hashlife.execution.dyadic_return_runs import (
    RunArithmeticWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.boundary_macros import (
    CollatzBoundaryMacro,
    validate_boundary_macro,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
)


def _overlap_length(
    start: int, stop: int, interval_start: int, interval_stop: int
) -> int:
    return max(0, min(stop, interval_stop) - max(start, interval_start))


def _alternating_slice(
    offset: int, length: int
) -> tuple[DyadicTerminalFieldAction, int]:
    """Slice ``1010...`` at an arbitrary offset using at most one power."""
    if length == 0:
        return DyadicTerminalFieldAction.identity(), 0
    action = DyadicTerminalFieldAction.identity()
    ones = 0
    if offset & 1:
        action = DyadicTerminalFieldAction.zero_run(1)
        offset += 1
        length -= 1
    pairs, final_one = divmod(length, 2)
    if pairs:
        motif = DyadicTerminalFieldAction.one_run(1).then(
            DyadicTerminalFieldAction.zero_run(1)
        )
        action = action.then(motif.power(pairs))
        ones += pairs
    if final_one:
        action = action.then(DyadicTerminalFieldAction.one_run(1))
        ones += 1
    return action, ones


def _slice_action(
    macro: CollatzBoundaryMacro, start: int, length: int
) -> tuple[DyadicTerminalFieldAction, int]:
    """Build one exact substring action from the admitted family grammar."""
    stop = start + length
    identity = DyadicTerminalFieldAction.identity()
    action = identity
    ones = 0

    def append_region(
        region_start: int,
        region_stop: int,
        symbol: int,
    ) -> None:
        nonlocal action, ones
        count = _overlap_length(start, stop, region_start, region_stop)
        if not count:
            return
        run = (
            DyadicTerminalFieldAction.one_run(count)
            if symbol
            else DyadicTerminalFieldAction.zero_run(count)
        )
        action = action.then(run)
        ones += count if symbol else 0

    if macro.family == "421":
        motif_start = 2
        motif_stop = 2 * macro.repetitions
        append_region(0, motif_start, 0)
        overlap_start = max(start, motif_start)
        overlap_stop = min(stop, motif_stop)
        if overlap_start < overlap_stop:
            pattern, count = _alternating_slice(
                overlap_start - motif_start, overlap_stop - overlap_start
            )
            action = action.then(pattern)
            ones += count
        append_region(motif_stop, motif_stop + 1, 1)
    elif macro.family == "4721":
        append_region(0, 1, 0)
        append_region(1, macro.normalized_symbols, 1)
    elif macro.family == "630":
        append_region(0, 1, 0)
        append_region(1, 2, 1)
        append_region(2, macro.normalized_symbols, 0)
    elif macro.family == "989":
        append_region(0, macro.normalized_symbols, 1)
    else:
        raise ValueError("unknown admitted Collatz boundary family")

    if action.steps != length:
        raise AssertionError("boundary grammar slice lost normalized symbols")
    return action, ones


def _highest_power_of_two(value: int) -> int:
    return 1 << (value.bit_length() - 1)


def _root_prefix_widths(maximum_width: int, anchor_bits: int) -> tuple[int, ...]:
    """Return root powers bounded by both macro extent and source support."""
    if type(maximum_width) is not int or type(anchor_bits) is not int:
        raise TypeError("boundary checkpoint extents require exact integers")
    if maximum_width < 0 or anchor_bits < 0:
        raise ValueError("boundary checkpoint extents must be nonnegative")
    limit = min(maximum_width, anchor_bits)
    widths: list[int] = []
    width = 8
    while width <= limit:
        widths.append(width)
        width <<= 1
    return tuple(widths)


def _preflight_slice(
    macro: CollatzBoundaryMacro,
    width: int,
    scratch: RunArithmeticWorkspace,
) -> None:
    # Coefficients of a normalized block have at most a small constant multiple
    # of its width in bits.  Include the exact source/endpoint operands and
    # simultaneous composition temporaries in the transient reservation.
    scratch.require_bits(64 * (macro.source.bit_length() + 8 * width + 64))


def _publish_boundary_macro_prefixes(
    macro: CollatzBoundaryMacro,
    macros: CollatzDyadicMacros,
    scratch: RunArithmeticWorkspace,
    *,
    anchor: int,
    normalized_offset: int,
    odd_offset: int,
) -> int:
    """Seed dyadic cache roots and the live frontier from one consumed macro.

    ``normalized_offset`` and ``odd_offset`` count normalized symbols and odd
    symbols already consumed from ``anchor``. Root prefixes are retained at
    every power of two crossed by this macro; the
    macro is also tiled into globally aligned dyadic intervals so its trailing
    region can join earlier/later work in the existing binary frontier.  At
    most seven symbols are left as a bounded affine remainder.

    Publication is opportunistic: a ledger refusal stops cache work after the
    exact macro has already advanced the query.  No endpoint is obtained by
    replaying scalar transitions.
    """
    validate_boundary_macro(macro)
    if (
        type(macros) is not CollatzDyadicMacros
        or type(scratch) is not RunArithmeticWorkspace
    ):
        raise TypeError(
            "boundary prefix publication requires its cache and scratch owner"
        )
    if not scratch.active:
        raise RuntimeError("boundary prefix arithmetic needs an active scratch scope")
    if (
        type(anchor) is not int
        or anchor <= 0
        or type(normalized_offset) is not int
        or normalized_offset < 0
        or type(odd_offset) is not int
        or not 0 <= odd_offset <= normalized_offset
    ):
        raise ValueError("boundary prefix origin is not authenticated")

    ledger: ResourceLedger = macros.ledger
    ledger.bump("collatz_boundary_prefix_macro_requests")
    ledger.bump(
        "collatz_boundary_prefix_source_operand_bits",
        macro.source.bit_length() + macro.endpoint.bit_length(),
    )
    root_publications = 0
    largest_root_prefix: tuple[int, DyadicTerminalFieldAction, int, int] | None = None
    cache_open = True

    if normalized_offset == 0 and macro.source == anchor:
        for width in _root_prefix_widths(macro.normalized_symbols, anchor.bit_length()):
            try:
                _preflight_slice(macro, width, scratch)
                action, ones = _slice_action(macro, 0, width)
                endpoint = action.endpoint(macro.source)
                ledger.bump("collatz_boundary_prefix_root_candidates")
                ledger.bump(
                    "collatz_boundary_prefix_action_operand_bits",
                    sum(
                        value.bit_length()
                        for value in (
                            action.gain,
                            action.offset,
                            action.sum_gain,
                            action.sum_offset,
                            endpoint,
                        )
                    ),
                )
                if endpoint <= 2:
                    macros.frontier.clear()
                    cache_open = False
                    break
                if macros.remember(macro.source, width, ones, endpoint):
                    root_publications += 1
                largest_root_prefix = (width, action, ones, endpoint)
            except BlockContextBudgetExceeded:
                macros.frontier.clear()
                cache_open = False
                ledger.bump("collatz_boundary_prefix_budget_bypasses")
                break
    # Publish cumulative root prefixes even when this macro starts after an
    # irregular run or a short alignment fragment. The binary frontier stores
    # only adjacent dyadic blocks and must discard such fragments; that is
    # independent of these exact root checkpoints. Each checkpoint is derived
    # from the admitted macro's closed grammar, not by replaying the source.
    if normalized_offset > 0 and cache_open:
        macro_end = normalized_offset + macro.normalized_symbols
        checkpoint = 1 << max(3, normalized_offset.bit_length())
        checkpoint_limit = min(macro_end, anchor.bit_length())
        while checkpoint <= checkpoint_limit:
            prefix_width = checkpoint - normalized_offset
            try:
                _preflight_slice(macro, prefix_width, scratch)
                action, prefix_ones = _slice_action(macro, 0, prefix_width)
                endpoint = action.endpoint(macro.source)
                total_ones = odd_offset + prefix_ones
                if not 0 <= total_ones <= checkpoint:
                    raise AssertionError(
                        "boundary checkpoint odd count exceeds its extent"
                    )
                ledger.bump("collatz_boundary_prefix_global_root_candidates")
                ledger.bump(
                    "collatz_boundary_prefix_action_operand_bits",
                    action.gain.bit_length()
                    + action.offset.bit_length()
                    + action.sum_gain.bit_length()
                    + action.sum_offset.bit_length()
                    + endpoint.bit_length(),
                )
                if endpoint <= 2:
                    macros.frontier.clear()
                    cache_open = False
                    break
                if macros.remember(anchor, checkpoint, total_ones, endpoint):
                    root_publications += 1
            except BlockContextBudgetExceeded:
                macros.frontier.clear()
                cache_open = False
                ledger.bump("collatz_boundary_prefix_budget_bypasses")
                break
            checkpoint *= 2

    position = normalized_offset
    local_offset = 0
    source = macro.source
    remaining = macro.normalized_symbols
    while remaining and cache_open:
        alignment_remainder = (-position) % 8
        if alignment_remainder:
            width = min(alignment_remainder, remaining)
        else:
            width = _highest_power_of_two(remaining)
            if position:
                width = min(width, position & -position)
            if width < 8:
                width = min(8 - (position % 8), remaining)
        try:
            _preflight_slice(macro, width, scratch)
            if (
                local_offset == 0
                and largest_root_prefix is not None
                and width == largest_root_prefix[0]
            ):
                _, action, ones, endpoint = largest_root_prefix
            else:
                action, ones = _slice_action(macro, local_offset, width)
                endpoint = action.endpoint(source)
            ledger.bump("collatz_boundary_prefix_slice_candidates")
            ledger.bump(
                "collatz_boundary_prefix_action_operand_bits",
                source.bit_length()
                + endpoint.bit_length()
                + action.gain.bit_length()
                + action.offset.bit_length(),
            )
            if width >= 8 and endpoint > 2:
                macros.observe(
                    source,
                    width,
                    ones,
                    endpoint,
                    anchor=anchor if position == 0 else 0,
                )
            elif endpoint <= 2:
                macros.frontier.clear()
                source = endpoint
                cache_open = False
                break
            else:
                # The existing binary frontier has no offset field. Dropping
                # even a short, exact affine slice without clearing it would
                # let later intervals join across a real temporal gap.
                macros.frontier.clear()
            source = endpoint
        except BlockContextBudgetExceeded:
            macros.frontier.clear()
            cache_open = False
            ledger.bump("collatz_boundary_prefix_budget_bypasses")
            break
        position += width
        local_offset += width
        remaining -= width

    if cache_open and source != macro.endpoint:
        raise AssertionError(
            "boundary slices do not reconstruct their admitted endpoint"
        )
    ledger.bump("collatz_boundary_prefix_root_publications", root_publications)
    return root_publications
