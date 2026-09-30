"""Explicit lossless carry-history accounting for reference sequence reports."""

from __future__ import annotations

from dataclasses import replace

from devtools.verification import require_exact_oracle
from devtools.verification.carry_action_quotient import CarryResetSignature
from number_compiler.api.sequence_types import ReverseAddCompilation
from number_compiler.arithmetic.carry.carry_itinerary import LiveCarryItinerary
from number_compiler.arithmetic.carry.event_memory import (
    carry_field,
    event_memory_horizon,
    pair_step,
)
from number_compiler.arithmetic.fields.radix import reverse_pair_sums


def with_carry_diagnostics(compilation: ReverseAddCompilation) -> ReverseAddCompilation:
    """Return independent proof metrics without changing production caches."""
    require_exact_oracle()
    spec = compilation.spec
    if spec.base < 3:
        raise ValueError("the carry-history proof requires base >= 3")
    pair = reverse_pair_sums(spec.seed, spec.base)
    rows: list[tuple[int, ...]] = []
    reset_bits = 0
    for index in range(spec.steps + 1):
        reset_bits = max(
            reset_bits,
            CarryResetSignature.from_pair(pair, base=spec.base).description_bits,
        )
        rows.append(carry_field(pair, base=spec.base))
        if index < spec.steps:
            pair, _ = pair_step(pair, spec.base)
    horizon = event_memory_horizon(spec.base)
    average: float | None = None
    maximum: int | None = None
    ratio: float | None = None
    if spec.steps >= horizon:
        live = LiveCarryItinerary.seed(rows[:horizon], base=spec.base)
        counts: list[int] = []
        live_bits = fixed_bits = 0
        for index in range(horizon, spec.steps + 1):
            counts.append(live.row_count)
            live_bits += live.charged_carry_bits
            fixed_bits += sum(len(row) for row in rows[index - horizon : index])
            if index < spec.steps:
                live = live.advance()
        average = sum(counts) / len(counts)
        maximum = max(counts)
        ratio = live_bits / fixed_bits if fixed_bits else 1.0
    return replace(
        compilation,
        live_rows_average=average,
        live_rows_max=maximum,
        live_carry_bits_ratio=ratio,
        carry_reset_max_bits=reset_bits,
    )
