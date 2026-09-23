"""Exact source-value and low-residue transport helpers."""

from __future__ import annotations

from operator import add, mul
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.consumer_pullback import PrefixSafety
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnLaw,
    DyadicReturnSupportID,
    _SupportNode,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicReturnImageWorkspace,
        _SourceNode,
    )


def _low_bits(value: int, width: int) -> int:
    """Return a low-bit slice without allocating a redundant wide mask."""
    if width == 0 or value == 0:
        return 0
    if value >= 0 and value.bit_length() <= width:
        return value
    return value & ((1 << width) - 1)


def source_value(workspace: DyadicReturnImageWorkspace, source: _SourceNode) -> int:
    if source.lift == 0:
        return source.residue
    return source.residue + (1 << source.precision) * source.lift


def cycle_phase_summaries(
    law: DyadicReturnLaw, phase: int, remainder: int
) -> tuple[PrefixSafety, int, PrefixSafety, int]:
    """Summarize one cycle and its demanded prefix without rotated arrays.

    Cycle descriptors are deliberately small, but these summaries sit on both
    the construction and first-failure paths.  Walking the authenticated state
    tuple once avoids rebuilding rotated state, weight, and prefix tuples for
    every large-cycle query.
    """
    cycle = law.cycle
    if cycle is None:
        raise ValueError("dyadic return law has no cycle")
    length = len(cycle.states)
    if not 0 <= phase < length or not 0 <= remainder < length:
        raise ValueError("dyadic return cycle phase is outside its descriptor")
    cycle_delta = cycle_minimum = cycle_odd = 0
    remainder_delta = remainder_minimum = remainder_odd = 0
    for offset in range(length):
        state = cycle.states[(phase + offset) % length]
        bit = state & 1
        cycle_delta += law.weights[bit]
        cycle_minimum = min(cycle_minimum, cycle_delta)
        cycle_odd += bit
        if offset < remainder:
            remainder_delta = cycle_delta
            remainder_minimum = cycle_minimum
            remainder_odd = cycle_odd
    return (
        PrefixSafety(cycle_delta, cycle_minimum),
        cycle_odd,
        PrefixSafety(remainder_delta, remainder_minimum),
        remainder_odd,
    )


def transport_low(
    workspace: DyadicReturnImageWorkspace,
    transfer: SkewTransfer[int],
    source_residue: int,
    after_width: int,
) -> int:
    """Transport only the demanded low residue through a skew."""
    if transfer.upper == 0:
        if transfer.offset % transfer.lower:
            raise ArithmeticError("dyadic return residue transport was not integral")
        value = transfer.offset // transfer.lower
        workspace._bump(
            "transport_operand_bits",
            max(
                1,
                source_residue.bit_length(),
                transfer.offset.bit_length(),
                transfer.lower.bit_length(),
                value.bit_length(),
            ),
        )
        return _low_bits(value, after_width)
    denominator_bits = transfer.lower.bit_length() - 1
    modulus_bits = denominator_bits + after_width
    if modulus_bits == 0:
        return 0
    # A short exact numerator is already its own residue. Do not allocate a
    # precision-sized modulus when a long requested horizon has a tiny source.
    numerator_bound = (
        max(
            transfer.upper.bit_length() + source_residue.bit_length(),
            transfer.offset.bit_length(),
        )
        + 1
    )
    if transfer.upper >= 0 and numerator_bound <= modulus_bits:
        numerator = transfer.upper * source_residue + transfer.offset
        if numerator >= 0:
            value, remainder = divmod(numerator, transfer.lower)
            if remainder:
                raise ArithmeticError(
                    "dyadic return residue transport was not integral"
                )
            workspace._bump("transport_short_numerator_demands")
            workspace._bump("transport_operand_bits", max(1, numerator_bound))
            return _low_bits(value, after_width)
    modulus = 1 << modulus_bits
    reduced_source = _low_bits(source_residue, modulus_bits)
    reduced_upper = _low_bits(transfer.upper, modulus_bits)
    reduced_offset = transfer.offset % modulus
    residue_numerator = (reduced_upper * reduced_source + reduced_offset) % modulus
    if residue_numerator % transfer.lower:
        raise ArithmeticError("dyadic return residue transport was not integral")
    workspace._bump(
        "transport_operand_bits",
        max(
            1,
            modulus_bits,
            source_residue.bit_length(),
            transfer.upper.bit_length(),
            transfer.offset.bit_length(),
            transfer.lower.bit_length(),
        ),
    )
    return _low_bits(residue_numerator // transfer.lower, after_width)


def residue_macro(
    workspace: DyadicReturnImageWorkspace, width: int, residue: int
) -> DyadicReturnSupportID:
    """Construct a bounded source-only macro by chronological squaring.

    A record admits every ``residue + 2**width * k``. Only the two width-one
    laws classify a branch. At most four low-residue base steps are evaluated;
    larger records substitute their left transfer in the right cylinder and
    compose complete skew/weight/branch effects. No full source orbit or
    supplied endpoint is evaluated. The explicit
    stack normalizes arithmetic *inside* a scheduler leaf; it publishes no
    source images and is not another execution scheduler.

    Memoization is exact on (width, residue), not on a carry/F5 projection.
    The bounded branch word is retained for existing demanded consumers.
    This construction can still create O(width) distinct records on a cold
    cylinder; it does not assert a finite temporal quotient for all sources.
    """
    workspace._validate_law()
    if (
        type(width) is not int
        or not 0 < width <= workspace.MAX_LEAF_STEPS
        or type(residue) is not int
        or residue < 0
        or residue.bit_length() > width
    ):
        raise ValueError("macro requires a bounded exact dyadic source cylinder")

    def bounded_base(span: int, source: int) -> _SupportNode:
        """Construct at most four exact source branches before any squaring.

        The low ``span`` source bits determine every branch. This fixed base
        reads no endpoint occurrence and stores no intermediate source word.
        The recurrence composes the skew coefficients chronologically while
        charging every primitive classification it performs.
        """
        current = source
        upper, offset, lower = 1, 0, 1
        odd_steps = delta = minimum = branch_word = 0
        for index in range(span):
            bit = current & 1
            gain = workspace.law.gains[bit]
            branch_offset = workspace.law.offsets[bit]
            prior = current
            current = (gain * current + branch_offset) // 2
            upper, offset, lower = (
                gain * upper,
                gain * offset + lower * branch_offset,
                lower * 2,
            )
            odd_steps += bit
            branch_word |= bit << index
            delta += workspace.law.weights[bit]
            minimum = min(minimum, delta)
            workspace._bump("macro_generator_admissions")
            workspace._bump("macro_bounded_base_steps")
            workspace._bump(
                "macro_bounded_base_operand_bits",
                sum(
                    max(1, abs(value).bit_length())
                    for value in (
                        prior,
                        current,
                        gain,
                        branch_offset,
                        upper,
                        offset,
                        lower,
                    )
                ),
            )
        workspace._bump("macro_bounded_base_calls")
        return _SupportNode(
            span,
            source,
            SkewTransfer(upper, offset, lower),
            odd_steps,
            delta,
            minimum,
            branch_word,
            None,
        )

    def lookup(key: tuple[int, int]) -> _SupportNode | None:
        return workspace.macros.get(key)

    def remember(node: _SupportNode) -> None:
        workspace.ledger.reserve(workspace.macro_owner, entries=1, nodes=1)
        try:
            workspace.macros[node.width, node.residue] = node
        except BaseException:
            workspace.ledger.release(workspace.macro_owner, entries=1, nodes=1)
            raise

    def push(span: int, source: int, left: _SupportNode | None) -> None:
        workspace.ledger.reserve(workspace.macro_stack_owner, entries=1, nodes=1)
        try:
            workspace.macro_stack.append((span, source, left))
        except BaseException:
            workspace.ledger.release(workspace.macro_stack_owner, entries=1, nodes=1)
            raise

    if workspace._closed:
        raise ValueError("disposed dyadic macro workspace")
    if workspace.macro_stack or workspace.macros:
        raise RuntimeError("nested or unfinished dyadic macro construction")
    workspace._bump("macro_requests")
    span, source = width, residue
    try:
        while True:
            cached = lookup((span, source))
            if cached is not None:
                workspace._bump("macro_hits")
                result = cached
            elif span <= 4:
                result = bounded_base(span, source)
                remember(result)
            else:
                push(span, source, None)
                span = 1 << ((span - 1).bit_length() - 1)
                source = _low_bits(source, span)
                continue
            while workspace.macro_stack:
                span, source, left = workspace.macro_stack.pop()
                workspace.ledger.release(
                    workspace.macro_stack_owner, entries=1, nodes=1
                )
                if left is None:
                    push(span, source, result)
                    span -= result.width
                    source = transport_low(workspace, result.transfer, source, span)
                    break
                right = result
                assert left.branch_word is not None and right.branch_word is not None
                transfer = left.transfer.then(right.transfer, multiply=mul, add=add)
                result = _SupportNode(
                    span,
                    source,
                    transfer,
                    left.odd_steps + right.odd_steps,
                    left.delta + right.delta,
                    min(left.minimum, left.delta + right.minimum),
                    left.branch_word | (right.branch_word << left.width),
                    None,
                )
                workspace._bump("macro_compositions")
                workspace._bump("macro_composed_extent", span)
                workspace._bump(
                    "macro_composition_operand_bits",
                    sum(
                        abs(v).bit_length()
                        for v in (
                            left.transfer.upper,
                            left.transfer.offset,
                            left.transfer.lower,
                            right.transfer.upper,
                            right.transfer.offset,
                            right.transfer.lower,
                        )
                    ),
                )
            else:
                return workspace._append_support(result)
    finally:
        remaining = len(workspace.macro_stack)
        workspace.macro_stack.clear()
        workspace.ledger.release(
            workspace.macro_stack_owner, entries=remaining, nodes=remaining
        )
        memo_count = len(workspace.macros)
        workspace.macros.clear()
        workspace.ledger.release(
            workspace.macro_owner, entries=memo_count, nodes=memo_count
        )
