"""Exact source-value and low-residue transport helpers."""

from __future__ import annotations

from operator import add, mul
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
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


def _residue_effect(
    workspace: DyadicReturnImageWorkspace, width: int, residue: int
) -> _SupportNode:
    """Return one exact bounded effect without publishing chronological support."""
    if not 0 < width <= workspace.MAX_LEAF_STEPS:
        raise ValueError("transient dyadic leaf exceeds the bounded leaf width")
    state = residue
    transfer = SkewTransfer(1, 0, 1)
    odd_steps = 0
    delta = 0
    minimum = 0
    branch_word = 0
    for index in range(width):
        bit = state & 1
        branch_word |= bit << index
        gain = workspace.law.gains[bit]
        offset = workspace.law.offsets[bit]
        numerator = gain * state + offset
        if numerator % 2:
            raise ArithmeticError("dyadic transient leaf was not integral")
        state = numerator // 2
        transfer = transfer.then(SkewTransfer(gain, offset, 2), multiply=mul, add=add)
        workspace._bump(
            "transient_leaf_operand_bits",
            sum(
                abs(value).bit_length()
                for value in (
                    state,
                    numerator,
                    gain,
                    offset,
                    transfer.upper,
                    transfer.offset,
                    transfer.lower,
                )
            ),
        )
        odd_steps += bit
        delta += workspace.law.weights[bit]
        minimum = min(minimum, delta)
    workspace._bump("transient_leaf_steps", width)
    return _SupportNode(
        width, residue, transfer, odd_steps, delta, minimum, branch_word, None
    )


def _balanced_residue_build(
    workspace: DyadicReturnImageWorkspace,
    width: int,
    residue: int,
    *,
    retain: bool,
) -> tuple[_SupportNode, DyadicReturnSupportID | None]:
    """Construct one balanced effect using a charged postorder work stack."""
    workspace._validate_law()
    if (
        type(width) is not int
        or width <= 0
        or type(residue) is not int
        or residue < 0
        or residue.bit_length() > width
    ):
        raise ValueError("balanced effect requires one exact dyadic source cylinder")
    stack = workspace.balanced_stack
    if workspace._closed or stack:
        raise RuntimeError("nested or disposed balanced dyadic construction")
    # This is an exact semantic cache for this one construction, never an
    # occurrence cache.  It is bounded independently of the represented
    # extent and released before publication.  Equal low cylinders at a
    # fixed span have identical complete effects under the pinned law.
    memo: dict[tuple[int, int], tuple[_SupportNode, DyadicReturnSupportID | None]] = {}
    MAX_MEMO = 64

    def remember(result: tuple[_SupportNode, DyadicReturnSupportID | None]) -> None:
        key = (result[0].width, result[0].residue)
        workspace._bump(
            "balanced_effect_memo_lookup_operand_bits",
            key[0].bit_length() + key[1].bit_length(),
        )
        if key in memo:
            return
        if len(memo) >= MAX_MEMO:
            evicted = next(iter(memo))
            workspace._bump(
                "balanced_effect_memo_lookup_operand_bits",
                evicted[0].bit_length() + evicted[1].bit_length(),
            )
            memo.pop(evicted)
            workspace.ledger.release(workspace.balanced_stack_owner, entries=1, nodes=1)
            workspace._bump("balanced_effect_memo_evictions")
        try:
            workspace.ledger.reserve(workspace.balanced_stack_owner, entries=1, nodes=1)
        except BlockContextBudgetExceeded:
            # A cache hit may save work, but its retention is never required
            # for a valid computation under a stricter request budget.
            return
        try:
            memo[key] = result
        except BaseException:
            workspace.ledger.release(workspace.balanced_stack_owner, entries=1, nodes=1)
            raise
        transfer = result[0].transfer
        workspace._bump("balanced_effect_memo_publications")
        workspace._bump(
            "balanced_effect_memo_operand_bits",
            sum(
                abs(value).bit_length()
                for value in (
                    result[0].residue,
                    transfer.upper,
                    transfer.offset,
                    transfer.lower,
                    result[0].delta,
                    result[0].minimum,
                )
            ),
        )

    def push(
        span: int,
        source: int,
        left: tuple[_SupportNode, DyadicReturnSupportID | None] | None,
    ) -> None:
        workspace.ledger.reserve(workspace.balanced_stack_owner, entries=1, nodes=1)
        try:
            stack.append((span, source, left))
        except BaseException:
            workspace.ledger.release(workspace.balanced_stack_owner, entries=1, nodes=1)
            raise
        workspace._bump("balanced_stack_frames")
        left_bits = (
            0
            if left is None
            else sum(
                abs(value).bit_length()
                for value in (
                    left[0].residue,
                    left[0].transfer.upper,
                    left[0].transfer.offset,
                    left[0].transfer.lower,
                    left[0].delta,
                    left[0].minimum,
                )
            )
        )
        workspace._bump(
            "balanced_stack_operand_bits",
            source.bit_length() + span.bit_length() + left_bits,
        )

    span, source = width, residue
    result: tuple[_SupportNode, DyadicReturnSupportID | None]
    try:
        while True:
            cached = memo.get((span, source))
            workspace._bump("balanced_effect_memo_lookups")
            workspace._bump(
                "balanced_effect_memo_lookup_operand_bits",
                span.bit_length() + source.bit_length(),
            )
            if cached is not None:
                result = cached
                workspace._bump("balanced_effect_memo_hits")
                workspace._bump("reused_temporal_extent", span)
            else:
                workspace._bump("balanced_effect_memo_misses")
            if cached is None and span <= workspace.MAX_LEAF_STEPS:
                if retain:
                    identity = residue_macro(workspace, span, source)
                    result = (
                        workspace.support_node(identity),
                        identity,
                    )
                else:
                    result = (_residue_effect(workspace, span, source), None)
                remember(result)
            elif cached is None:
                push(span, source, None)
                span = 1 << ((span - 1).bit_length() - 1)
                source = _low_bits(source, span)
                continue

            while stack:
                parent_span, parent_source, left = stack.pop()
                workspace.ledger.release(
                    workspace.balanced_stack_owner, entries=1, nodes=1
                )
                if left is None:
                    push(parent_span, parent_source, result)
                    span = parent_span - result[0].width
                    source = transport_low(
                        workspace, result[0].transfer, parent_source, span
                    )
                    break
                right = result
                left_node, left_id = left
                right_node, right_id = right
                transfer = left_node.transfer.then(
                    right_node.transfer, multiply=mul, add=add
                )
                operand_bits = sum(
                    abs(value).bit_length()
                    for value in (
                        left_node.transfer.upper,
                        left_node.transfer.offset,
                        left_node.transfer.lower,
                        right_node.transfer.upper,
                        right_node.transfer.offset,
                        right_node.transfer.lower,
                    )
                )
                if retain:
                    assert left_id is not None and right_id is not None
                    children = (left_id, right_id)
                else:
                    children = None
                node = _SupportNode(
                    parent_span,
                    parent_source,
                    transfer,
                    left_node.odd_steps + right_node.odd_steps,
                    left_node.delta + right_node.delta,
                    min(left_node.minimum, left_node.delta + right_node.minimum),
                    None,
                    children,
                    None,
                    not retain,
                )
                if retain:
                    node_id = workspace._append_support(node)
                    suffix = "balanced_macro"
                else:
                    node_id = None
                    suffix = "balanced_effect"
                workspace._bump(f"{suffix}_compositions")
                workspace._bump(f"{suffix}_composed_extent", parent_span)
                workspace._bump(f"{suffix}_composition_operand_bits", operand_bits)
                result = (node, node_id)
                remember(result)
            else:
                return result
    finally:
        pending = len(stack)
        if pending:
            stack.clear()
            workspace.ledger.release(
                workspace.balanced_stack_owner, entries=pending, nodes=pending
            )
        retained = len(memo)
        if retained:
            memo.clear()
            workspace.ledger.release(
                workspace.balanced_stack_owner, entries=retained, nodes=retained
            )


def balanced_residue_effect(
    workspace: DyadicReturnImageWorkspace, width: int, residue: int
) -> _SupportNode:
    """Build an exact effect with logarithmic charged transient stack depth."""
    workspace._bump("balanced_effect_requests")
    node, identity = _balanced_residue_build(workspace, width, residue, retain=False)
    assert identity is None
    return node


def balanced_residue_macro(
    workspace: DyadicReturnImageWorkspace, width: int, residue: int
) -> DyadicReturnSupportID:
    """Publish exact chronological support through the same balanced worklist."""
    workspace._bump("balanced_macro_requests")
    _node, identity = _balanced_residue_build(workspace, width, residue, retain=True)
    assert identity is not None
    return identity


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
