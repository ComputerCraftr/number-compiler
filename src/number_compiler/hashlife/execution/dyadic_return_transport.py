"""Exact source-value and low-residue transport helpers."""

from __future__ import annotations

from operator import add, mul
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.dyadic_return_records import (
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
    if value.bit_length() <= width:
        return value
    return value & ((1 << width) - 1)


def source_value(workspace: DyadicReturnImageWorkspace, source: _SourceNode) -> int:
    if source.lift == 0:
        return source.residue
    return source.residue + (1 << source.precision) * source.lift


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
    return (residue_numerator // transfer.lower) & ((1 << after_width) - 1)


def residue_macro(
    workspace: DyadicReturnImageWorkspace, width: int, residue: int
) -> DyadicReturnSupportID:
    """Construct a bounded source-only macro by chronological squaring.

    A record admits every ``residue + 2**width * k``. Only the two width-one
    laws classify a branch. Larger records substitute their left transfer in
    the right cylinder, then compose complete skew/weight/branch effects.
    Neither a scalar orbit nor a supplied endpoint is evaluated. The explicit
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
        or not 0 <= residue < 1 << width
    ):
        raise ValueError("macro requires a bounded exact dyadic source cylinder")

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
            elif span == 1:
                transfer = SkewTransfer(
                    workspace.law.gains[source], workspace.law.offsets[source], 2
                )
                delta = workspace.law.weights[source]
                result = _SupportNode(
                    1, source, transfer, source, delta, min(0, delta), source, None
                )
                workspace._bump("macro_generator_admissions")
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
                # D4 is the reusable alphabet. Larger temporary effects are
                # normalized to one return, not retained as an internal tree.
                if span <= 4:
                    remember(result)
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
