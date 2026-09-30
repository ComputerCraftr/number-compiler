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
    # One demanded clock supplies both 3^(-n) and -3^(-(n+1)).
    # Multiplying the full endpoint before reducing it copies irrelevant
    # high source bits into a precision-limited observation.
    clock_exponent = arithmetic.returns + 1
    clock = InverseThreeClock(clock_precision, clock_exponent)
    inverse_next = clock.inverse_unit % modulus
    scale = 3 * inverse_next % modulus
    source_residue = d & (modulus - 1)
    normalized = source_residue * scale % modulus
    root = -inverse_next % modulus
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
    # These are observational operand-size totals, not budget admission.
    # The modular power consumes the period-reduced clock phase; preserve
    # the unreduced exponent's size separately so normalization stays visible.
    arithmetic.ledger.bump(
        "tangent_modular_power_exponent_bits", clock.phase.bit_length()
    )
    arithmetic.ledger.bump(
        "tangent_clock_input_exponent_bits", clock_exponent.bit_length()
    )
    arithmetic.ledger.bump("tangent_inverse_clock_demands")
    arithmetic.ledger.bump(
        "tangent_modular_operand_bits",
        max(1, d.bit_length())
        + max(1, source_residue.bit_length())
        + max(1, scale.bit_length())
        + 3 * (clock_precision + 1),
    )
    return data
