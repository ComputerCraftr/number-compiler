"""Source-bound Mahler tangent observations; finite agreement is not closure."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.antihydra.runtime import (
    ArithmeticResult,
    Run,
    authenticated_arithmetic_result,
)
from number_compiler.sequences.collatz.inverse_three_clock import InverseThreeClock


def tangent(result: Run | ArithmeticResult, precision: int) -> dict[str, object]:
    arithmetic = authenticated_arithmetic_result(result)
    require_integer(precision, "tangent precision", 1, 4096)
    d = arithmetic.h - 1
    data: dict[str, object] = {
        "source": 7,
        "timestamp_macro_returns": arithmetic.returns,
        "consumed_centered_odd_events": arithmetic.odd_events,
        "slack": arithmetic.balance,
        "at_odd_seam": bool(d & 1),
        "all_time_barrier_proved": False,
        "moving_cylinder": {
            "source_depth": arithmetic.returns + precision,
            "two_exponent": precision,
            "three_exponent": arithmetic.returns,
            "representative": d,
        },
    }
    if not d & 1:
        data["even_run_depth"] = v2_positive(d)
        return data
    modulus = 1 << precision
    clock_precision = max(3, precision)
    inv3 = InverseThreeClock(clock_precision, 1).inverse_unit % modulus
    scale = (
        InverseThreeClock(clock_precision, arithmetic.returns).inverse_unit % modulus
    )
    normalized = d * scale % modulus
    root = -scale * inv3 % modulus
    difference = (normalized - root) % modulus
    matched = v2_positive(difference) if difference else precision
    data.update(
        precision=precision,
        normalized_residue=normalized,
        clock_root=root,
        matched_bits=matched,
        matched_radix64_cells=matched // 6,
        resolved=bool(difference),
    )
    if difference:
        data.update(
            gap=matched,
            child_precision=precision - matched,
            child_normalized_residue=difference >> matched,
        )
    else:
        data["required_next_precision"] = precision + 6
    arithmetic.ledger.counters["tangent_modular_power_exponent_bits"] = (
        arithmetic.ledger.counters.get("tangent_modular_power_exponent_bits", 0)
        + arithmetic.returns.bit_length()
    )
    return data
