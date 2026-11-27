"""Exact least CF prefix over the chronological powers-of-five stream."""

from __future__ import annotations

import os
from collections.abc import Callable
from contextlib import ExitStack
from dataclasses import dataclass
from fractions import Fraction
from typing import TYPE_CHECKING, Protocol

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra import mahler_cf_fractional_path as fractional
from number_compiler.sequences.antihydra.mahler_continued_fraction import (
    continuant_rows,
    validate_cf_resources,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.mahler_pow5_source import Pow5CFRow

_MAX_CYLINDER_HORIZON = 4096
_SPATIAL_CYLINDER_MIN_HORIZON = 64


class _OrderedCFBlock(Protocol):
    @property
    def coefficient_count(self) -> int: ...

    @property
    def product(self) -> Matrix2: ...

    def segment(self, start: int, length: int) -> Matrix2: ...


@dataclass(frozen=True, slots=True)
class _PointedRowSlice:
    row: Pow5CFRow
    start: int
    coefficient_count: int

    @property
    def product(self) -> Matrix2:
        return self.segment(0, self.coefficient_count)

    def segment(self, start: int, length: int) -> Matrix2:
        require_integer(start, "pointed segment start", 0, self.coefficient_count)
        require_integer(
            length, "pointed segment length", 0, self.coefficient_count - start
        )
        return self.row.segment(self.start + start, length)


def _ordered_blocks(
    resources: ExitStack,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    horizon: int,
    *,
    shared_cache: bool,
) -> Callable[[int, int, int], _OrderedCFBlock]:
    # A packed request can hold both the current and staging grammar,
    # including their continuants. Tight or already occupied ledgers keep
    # the existing pointed admission, from its first source row onward.
    try:
        ledger.check_capacity(nodes=10_000, entries=512)
    except BlockContextBudgetExceeded:
        from number_compiler.sequences.antihydra.mahler_pow5_source import Pow5CFSource

        pointed = resources.enter_context(
            Pow5CFSource(ledger, shared_cache=shared_cache)
        )
        row: Pow5CFRow | None = None
        offset = 0

        def next_pointed(count: int, limit: int, _remaining: int) -> _PointedRowSlice:
            nonlocal row, offset
            if row is None or offset == row.width:
                row = pointed.next_row()
                offset = 0
            width = row.width
            scratch.require_bits(64 * (horizon + count + width + row.exponent + 128))
            length = 1 if width < 32 else min(width - offset, limit)
            block = _PointedRowSlice(row, offset, length)
            offset += length
            return block

        return next_pointed

    from number_compiler.sequences.antihydra.mahler_pow5_ordered_blocks import (
        Pow5OrderedBlockSource,
    )

    reciprocal = (
        horizon < _SPATIAL_CYLINDER_MIN_HORIZON
        or os.environ.get("NUMBER_COMPILER_ENABLE_CF_RECIPROCAL") == "1"
    )
    packed = resources.enter_context(
        Pow5OrderedBlockSource(
            ledger,
            shared_cache=shared_cache,
            spatial=not reciprocal,
            reciprocal=reciprocal,
        )
    )

    def next_packed(count: int, limit: int, remaining: int) -> _OrderedCFBlock:
        scratch.require_bits(64 * (horizon + count + 128))
        # Widen undecided prefixes, then narrow the lookahead near the end
        # to avoid compiling rows beyond the likely decisive block.
        rows = 1 if count == 0 else max(1, min(4, (remaining + 127) // 128))
        block = packed.next_block(rows, limit)
        scratch.require_bits(64 * (horizon + count + block.coefficient_count + 128))
        return block

    return next_packed


def _interval(matrix: Matrix2) -> tuple[Fraction, Fraction]:
    q, previous_q, p, previous_p = matrix.entries
    if q <= 0 or q + previous_q <= 0:
        raise ArithmeticError("continued-fraction interval requires a source prefix")
    endpoints = Fraction(p, q), Fraction(p + previous_p, q + previous_q)
    low, high = sorted(endpoints)
    if low == high:
        raise ArithmeticError("continued-fraction continuant is singular")
    return low, high


def continued_fraction_cylinder(
    horizon: int,
    max_coefficients: int,
    *,
    ledger: ResourceLedger,
    shared_cache: bool = True,
) -> dict[str, object]:
    """Select the first exact coefficient prefix forcing the physical horizon."""
    validate_cf_resources(ledger, shared_cache)
    require_integer(horizon, "physical safety horizon", 0, _MAX_CYLINDER_HORIZON)
    require_integer(max_coefficients, "coefficient budget", 1, 100000)
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "mahler-cf-cylinder")
    reason = "continued-fraction coefficient budget exhausted"
    action = fractional.FractionalPath()
    count = 0
    prefix = Matrix2.identity()
    chart_scratch: RunArithmeticWorkspace | None = None
    chart_refused = False
    wide_refused = False
    with scratch.scope(), ExitStack() as resources:
        next_block = _ordered_blocks(
            resources, ledger, scratch, horizon, shared_cache=shared_cache
        )
        while count < max_coefficients:
            try:
                block = next_block(
                    count, max_coefficients - count, horizon - action.extent
                )
            except StopIteration:
                reason = "continued-fraction source exponent exceeds its bound"
                break
            length = block.coefficient_count
            product = prefix.multiply(block.product)
            low, high = _interval(product)
            use_chart = (
                not chart_refused
                and horizon >= 512
                and max_coefficients >= 128
                and action.extent >= 32
            )
            if use_chart:
                if chart_scratch is None:
                    chart_scratch = RunArithmeticWorkspace.for_ledger(
                        ledger, "mahler-cf-branch-chart"
                    )
                with chart_scratch.scope():
                    wide = horizon >= 2048 and not wide_refused
                    try:
                        if wide:
                            try:
                                chart_scratch.require_bits(
                                    fractional.PACKED_CHART_SCRATCH_BITS
                                )
                            except BlockContextBudgetExceeded:
                                wide = False
                                wide_refused = True
                        if not wide:
                            chart_scratch.require_bits(
                                fractional.BRANCH_CHART_SCRATCH_BITS
                            )
                    except BlockContextBudgetExceeded:
                        # Optional pre-work capacity refusal leaves the exact
                        # source and its existing scalar action untouched.
                        chart_refused = True
                    else:
                        if wide:
                            action.packed_chart = fractional.packed_branch_chart()
                        else:
                            action.chart = fractional.branch_chart()
                        try:
                            action.extend(low, high, horizon)
                        finally:
                            action.chart = None
                            action.packed_chart = None
                if chart_refused:
                    action.extend(low, high, horizon)
            else:
                action.extend(low, high, horizon)
            if action.extent < horizon:
                prefix = product
                count += length
                continue
            if not action.contains(low, high):
                raise ArithmeticError(
                    "continued-fraction prefix lost its complete source guard"
                )

            # All previous blocks stopped before forcing the full horizon.
            # This block fixes the complete path, so its exact guard decides
            # which inside prefix is sufficient without replaying the path.
            lower = 0
            lower_product = prefix
            while lower + 1 < length:
                middle = (lower + length) // 2
                candidate = lower_product.multiply(block.segment(lower, middle - lower))
                smaller_low, smaller_high = _interval(candidate)
                if action.contains(smaller_low, smaller_high):
                    product = candidate
                    low, high = smaller_low, smaller_high
                    length = middle
                else:
                    lower = middle
                    lower_product = candidate
            endpoint_lower = Fraction(*action.endpoint(low))
            endpoint_upper = Fraction(*action.endpoint(high))
            return {
                "status": "available",
                "source_law": "decimal-powers-of-five",
                "clock_unit": "physical-recurrence-ticks",
                "horizon": horizon,
                "coefficient_count": count + length,
                "matrix": continuant_rows(product),
                "fraction_lower": {
                    "numerator": low.numerator,
                    "denominator": low.denominator,
                },
                "fraction_upper": {
                    "numerator": high.numerator,
                    "denominator": high.denominator,
                },
                "endpoint_lower": {
                    "numerator": endpoint_lower.numerator,
                    "denominator": endpoint_lower.denominator,
                },
                "endpoint_upper": {
                    "numerator": endpoint_upper.numerator,
                    "denominator": endpoint_upper.denominator,
                },
                "source_residue": action.residue(),
                "source_modulus": action.modulus,
                "weighted_innovation": action.innovation,
                "authority_scope": "bounded-cf-fractional-cylinder",
            }
    return {
        "status": "unknown",
        "reason": reason,
        "source_law": "decimal-powers-of-five",
        "coefficient_count": count,
        "certified_physical_ticks": action.extent,
    }
