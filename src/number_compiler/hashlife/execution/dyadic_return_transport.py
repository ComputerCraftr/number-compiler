"""Exact source-value and low-residue transport helpers."""

from __future__ import annotations

from operator import add, mul
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    PrefixSafety,
    compose_prefix_safety_values,
)
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnLaw,
    DyadicReturnSupportID,
    DyadicReturnSupportRecord,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicReturnImageWorkspace,
    )
    from number_compiler.hashlife.execution.dyadic_return_records import (
        DyadicReturnSourceRecord,
    )


def low_bits(value: int, width: int) -> int:
    """Return a low-bit slice without allocating a redundant wide mask."""
    if width == 0 or value == 0:
        return 0
    if value >= 0 and value.bit_length() <= width:
        return value
    return value & ((1 << width) - 1)


def source_value(
    workspace: DyadicReturnImageWorkspace, source: DyadicReturnSourceRecord
) -> int:
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
        workspace.bump_metric(
            "transport_operand_bits",
            max(
                1,
                source_residue.bit_length(),
                transfer.offset.bit_length(),
                transfer.lower.bit_length(),
                value.bit_length(),
            ),
        )
        return low_bits(value, after_width)
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
            workspace.bump_metric("transport_short_numerator_demands")
            workspace.bump_metric("transport_operand_bits", max(1, numerator_bound))
            return low_bits(value, after_width)
    modulus = 1 << modulus_bits
    reduced_source = low_bits(source_residue, modulus_bits)
    reduced_upper = low_bits(transfer.upper, modulus_bits)
    reduced_offset = transfer.offset % modulus
    residue_numerator = (reduced_upper * reduced_source + reduced_offset) % modulus
    if residue_numerator % transfer.lower:
        raise ArithmeticError("dyadic return residue transport was not integral")
    workspace.bump_metric(
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
    return low_bits(residue_numerator // transfer.lower, after_width)


def _balanced_residue_build(
    workspace: DyadicReturnImageWorkspace,
    width: int,
    residue: int,
    *,
    retain: bool,
    keep_memo: bool = False,
) -> tuple[DyadicReturnSupportRecord, DyadicReturnSupportID | None]:
    """Construct one balanced effect using a charged postorder work stack."""
    workspace.validate_law()
    if (
        type(width) is not int
        or width <= 0
        or type(residue) is not int
        or residue < 0
        or residue.bit_length() > width
    ):
        raise ValueError("balanced effect requires one exact dyadic source cylinder")
    stack = workspace.balanced_stack
    if workspace.closed or stack or (workspace.macros and not keep_memo):
        raise RuntimeError("nested or disposed balanced dyadic construction")
    # This is an exact semantic cache for this one construction, never an
    # occurrence cache.  It is bounded independently of the represented
    # extent and released before publication.  Equal low cylinders at a
    # fixed span have identical complete effects under the pinned law.
    memo: dict[
        tuple[int, int], tuple[DyadicReturnSupportRecord, DyadicReturnSupportID | None]
    ] = {}
    MAX_MEMO = 64

    def remember(
        result: tuple[DyadicReturnSupportRecord, DyadicReturnSupportID | None],
    ) -> None:
        key = (result[0].width, result[0].residue)
        workspace.bump_metric(
            "balanced_effect_memo_lookup_operand_bits",
            key[0].bit_length() + key[1].bit_length(),
        )
        if key in memo:
            return
        if len(memo) >= MAX_MEMO:
            evicted = next(iter(memo))
            workspace.bump_metric(
                "balanced_effect_memo_lookup_operand_bits",
                evicted[0].bit_length() + evicted[1].bit_length(),
            )
            memo.pop(evicted)
            workspace.ledger.release(workspace.balanced_stack_owner, entries=1, nodes=1)
            workspace.bump_metric("balanced_effect_memo_evictions")
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
        workspace.bump_metric("balanced_effect_memo_publications")
        workspace.bump_metric(
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
        left: tuple[DyadicReturnSupportRecord, DyadicReturnSupportID | None] | None,
    ) -> None:
        workspace.ledger.reserve(workspace.balanced_stack_owner, entries=1, nodes=1)
        try:
            stack.append((span, source, left))
        except BaseException:
            workspace.ledger.release(workspace.balanced_stack_owner, entries=1, nodes=1)
            raise
        workspace.bump_metric("balanced_stack_frames")
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
        workspace.bump_metric(
            "balanced_stack_operand_bits",
            source.bit_length() + span.bit_length() + left_bits,
        )

    span, source = width, residue
    try:
        while True:
            cached = memo.get((span, source))
            workspace.bump_metric("balanced_effect_memo_lookups")
            workspace.bump_metric(
                "balanced_effect_memo_lookup_operand_bits",
                span.bit_length() + source.bit_length(),
            )
            if cached is not None:
                current_result = cached
                workspace.bump_metric("balanced_effect_memo_hits")
                workspace.bump_metric("reused_temporal_extent", span)
            elif span <= workspace.MAX_LEAF_STEPS:
                workspace.bump_metric("balanced_effect_memo_misses")
                if retain:
                    identity = residue_macro(workspace, span, source, retain_cache=True)
                    current_result = (
                        workspace.support_node(identity),
                        identity,
                    )
                else:
                    current_result = (
                        finite_residue_effect(
                            workspace, span, source, retain_cache=True
                        ),
                        None,
                    )
            else:
                workspace.bump_metric("balanced_effect_memo_misses")
                push(span, source, None)
                span, source = _first_half_residue(span, source)
                continue
            result = current_result
            if cached is None:
                remember(result)

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
                safety_delta, safety_minimum = compose_prefix_safety_values(
                    left_node.delta,
                    left_node.minimum,
                    right_node.delta,
                    right_node.minimum,
                )
                node = DyadicReturnSupportRecord(
                    parent_span,
                    parent_source,
                    transfer,
                    left_node.odd_steps + right_node.odd_steps,
                    safety_delta,
                    safety_minimum,
                    None,
                    children,
                    None,
                    not retain,
                )
                if retain:
                    node_id = workspace.append_support(node)
                    suffix = "balanced_macro"
                else:
                    node_id = None
                    suffix = "balanced_effect"
                workspace.bump_metric(f"{suffix}_compositions")
                workspace.bump_metric(f"{suffix}_composed_extent", parent_span)
                workspace.bump_metric(
                    f"{suffix}_composition_operand_bits", operand_bits
                )
                result = (node, node_id)
                remember(result)
            else:
                return result
    finally:
        if not keep_memo:
            clear_finite_support_cache(workspace)
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
    workspace: DyadicReturnImageWorkspace,
    width: int,
    residue: int,
    *,
    retain_cache: bool = False,
) -> DyadicReturnSupportRecord:
    """Build an exact effect with logarithmic charged transient stack depth."""
    workspace.bump_metric("balanced_effect_requests")
    node, identity = _balanced_residue_build(
        workspace, width, residue, retain=False, keep_memo=retain_cache
    )
    assert identity is None
    return node


def balanced_residue_macro(
    workspace: DyadicReturnImageWorkspace,
    width: int,
    residue: int,
    *,
    retain_cache: bool = False,
) -> DyadicReturnSupportID:
    """Publish exact chronological support through the same balanced worklist."""
    workspace.bump_metric("balanced_macro_requests")
    _node, identity = _balanced_residue_build(
        workspace, width, residue, retain=True, keep_memo=retain_cache
    )
    assert identity is not None
    return identity


def _build_residue_effect(
    workspace: DyadicReturnImageWorkspace,
    width: int,
    residue: int,
    *,
    macro: bool = False,
    keep_memo: bool = False,
) -> DyadicReturnSupportRecord:
    """Compose a bounded leaf from exact finite cylinders under its pinned law.

    Only four-bit cold atoms classify branches. Eight-bit atoms are their
    chronological compositions, and the construction-local memo admits only
    these finite effects. It never consumes a source endpoint or occurrence.
    """
    workspace.validate_law()
    if (
        type(width) is not int
        or not 0 < width <= workspace.MAX_LEAF_STEPS
        or type(residue) is not int
        or residue < 0
        or residue.bit_length() > width
    ):
        raise ValueError("macro requires a bounded exact dyadic source cylinder")

    def bounded_base(span: int, source: int) -> DyadicReturnSupportRecord:
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
            workspace.bump_metric("finite_block_cold_steps")
            if macro:
                workspace.bump_metric("macro_generator_admissions")
            workspace.bump_metric(
                "macro_bounded_base_steps" if macro else "transient_leaf_steps"
            )
            workspace.bump_metric(
                "macro_bounded_base_operand_bits"
                if macro
                else "transient_leaf_operand_bits",
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
        workspace.bump_metric("finite_block_cold_atoms")
        if macro:
            workspace.bump_metric("macro_bounded_base_calls")
        return DyadicReturnSupportRecord(
            span,
            source,
            SkewTransfer(upper, offset, lower),
            odd_steps,
            delta,
            minimum,
            branch_word,
            None,
        )

    def key(span: int, source: int) -> tuple[object, ...]:
        return (workspace.owner, workspace.law_snapshot, span, source)

    def lookup(span: int, source: int) -> DyadicReturnSupportRecord | None:
        if span > 8:
            return None
        workspace.bump_metric("finite_block_lookups")
        workspace.bump_metric(
            "finite_block_lookup_operand_bits", span.bit_length() + source.bit_length()
        )
        cached = workspace.macros.get(key(span, source))
        workspace.bump_metric(
            "finite_block_hits" if cached is not None else "finite_block_misses"
        )
        return cached

    def remember(node: DyadicReturnSupportRecord) -> None:
        if node.width > 8:
            return
        if len(workspace.macros) >= 256:
            evicted = next(iter(workspace.macros))
            workspace.macros.pop(evicted)
            workspace.ledger.release(workspace.macro_owner, entries=1, nodes=1)
            workspace.bump_metric("finite_block_evictions")
        try:
            workspace.ledger.reserve(workspace.macro_owner, entries=1, nodes=1)
        except BlockContextBudgetExceeded:
            return
        try:
            workspace.macros[key(node.width, node.residue)] = node
        except BaseException:
            workspace.ledger.release(workspace.macro_owner, entries=1, nodes=1)
            raise
        workspace.bump_metric("finite_block_publications")
        workspace.bump_metric(
            "finite_block_retained_operand_bits",
            sum(
                max(1, abs(value).bit_length())
                for value in (
                    node.width,
                    node.residue,
                    node.transfer.upper,
                    node.transfer.offset,
                    node.transfer.lower,
                    node.odd_steps,
                    node.delta,
                    node.minimum,
                    node.branch_word or 0,
                )
            ),
        )

    def compose(
        left: DyadicReturnSupportRecord,
        right: DyadicReturnSupportRecord,
        span: int,
        source: int,
    ) -> DyadicReturnSupportRecord:
        assert left.branch_word is not None and right.branch_word is not None
        transfer = left.transfer.then(right.transfer, multiply=mul, add=add)
        safety_delta, safety_minimum = compose_prefix_safety_values(
            left.delta, left.minimum, right.delta, right.minimum
        )
        result = DyadicReturnSupportRecord(
            span,
            source,
            transfer,
            left.odd_steps + right.odd_steps,
            safety_delta,
            safety_minimum,
            left.branch_word | (right.branch_word << left.width),
            None,
        )
        workspace.bump_metric(
            "macro_compositions" if macro else "finite_block_compositions"
        )
        workspace.bump_metric(
            "macro_composed_extent" if macro else "finite_block_composed_extent", span
        )
        workspace.bump_metric(
            "macro_composition_operand_bits"
            if macro
            else "finite_block_composition_operand_bits",
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
        return result

    def push(span: int, source: int, left: DyadicReturnSupportRecord | None) -> None:
        workspace.ledger.reserve(workspace.macro_stack_owner, entries=1, nodes=1)
        try:
            workspace.macro_stack.append((span, source, left))
        except BaseException:
            workspace.ledger.release(workspace.macro_stack_owner, entries=1, nodes=1)
            raise

    if workspace.closed:
        raise ValueError("disposed dyadic macro workspace")
    if workspace.macro_stack or (workspace.macros and not keep_memo):
        raise RuntimeError("nested or unfinished dyadic macro construction")
    if macro:
        workspace.bump_metric("macro_requests")

    def atom(span: int, source: int) -> DyadicReturnSupportRecord:
        cached = lookup(span, source)
        if cached is not None:
            return cached
        if span <= 4:
            result = bounded_base(span, source)
        else:
            left_source = low_bits(source, 4)
            left = lookup(4, left_source)
            if left is None:
                left = bounded_base(4, left_source)
                remember(left)
            right_span = span - 4
            right_source = transport_low(workspace, left.transfer, source, right_span)
            right = lookup(right_span, right_source)
            if right is None:
                right = bounded_base(right_span, right_source)
                remember(right)
            result = compose(left, right, span, source)
        remember(result)
        return result

    if not macro:
        # A fixed-width leaf needs only one running complete effect. Keeping
        # this scalar accumulator avoids making optional atom retention a
        # prerequisite under a budget that only admits the outer work stack.
        try:
            first_width = min(8, width)
            result = atom(first_width, low_bits(residue, first_width))
            while result.width < width:
                span = min(8, width - result.width)
                source = transport_low(workspace, result.transfer, residue, span)
                right = atom(span, source)
                result = compose(result, right, result.width + span, residue)
            return result
        finally:
            if not keep_memo:
                clear_finite_support_cache(workspace)

    span, source = width, residue
    try:
        while True:
            cached = lookup(span, source)
            if cached is not None:
                if macro:
                    workspace.bump_metric("macro_hits")
                result = cached
            elif span <= 4:
                result = bounded_base(span, source)
                remember(result)
            else:
                push(span, source, None)
                span, source = _first_half_residue(span, source)
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
                result = compose(left, result, span, source)
                remember(result)
            else:
                return result
    finally:
        remaining = len(workspace.macro_stack)
        workspace.macro_stack.clear()
        workspace.ledger.release(
            workspace.macro_stack_owner, entries=remaining, nodes=remaining
        )
        if not keep_memo:
            clear_finite_support_cache(workspace)


def clear_finite_support_cache(workspace: DyadicReturnImageWorkspace) -> None:
    """Release construction-local residue atoms and their exact ledger charge."""
    count = len(workspace.macros)
    workspace.macros.clear()
    workspace.ledger.release(workspace.macro_owner, entries=count, nodes=count)


def finite_residue_effect(
    workspace: DyadicReturnImageWorkspace,
    width: int,
    residue: int,
    *,
    retain_cache: bool = False,
) -> DyadicReturnSupportRecord:
    """Compute one exact finite-cylinder action, optionally retaining its memo."""
    return _build_residue_effect(
        workspace,
        width,
        residue,
        keep_memo=retain_cache,
    )


def residue_macro(
    workspace: DyadicReturnImageWorkspace,
    width: int,
    residue: int,
    *,
    retain_cache: bool = False,
) -> DyadicReturnSupportID:
    """Publish bounded chronological support from the shared finite algebra."""
    result = _build_residue_effect(
        workspace, width, residue, macro=True, keep_memo=retain_cache
    )
    return workspace.append_support(result)


def _first_half_residue(span: int, source: int) -> tuple[int, int]:
    half = 1 << ((span - 1).bit_length() - 1)
    return half, low_bits(source, half)
