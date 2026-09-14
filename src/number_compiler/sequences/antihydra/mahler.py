"""Source-bound Mahler tangent observations; finite agreement is not closure."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.sequences.antihydra.runtime import Run


def tangent(result: Run, precision: int) -> dict[str, object]:
    result.require_source()
    require_integer(precision, "tangent precision", 1, 4096)
    if result.halted:
        raise ValueError("halted source has no returning Mahler seam")
    d = result.h - 1
    data: dict[str, object] = {
        "source": 7,
        "timestamp_macro_returns": result.returns,
        "consumed_centered_odd_events": result.odd_events,
        "slack": result.balance,
        "at_odd_seam": bool(d & 1),
        "all_time_barrier_proved": False,
        "moving_cylinder": {
            "source_depth": result.returns + precision,
            "two_exponent": precision,
            "three_exponent": result.returns,
            "representative": d,
        },
    }
    if not d & 1:
        data["even_run_depth"] = (d & -d).bit_length() - 1
        return data
    modulus = 1 << precision
    inv3 = pow(3, -1, modulus)
    scale = pow(inv3, result.returns, modulus)
    normalized = d * scale % modulus
    root = -scale * inv3 % modulus
    difference = (normalized - root) % modulus
    matched = (difference & -difference).bit_length() - 1 if difference else precision
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
    result.ledger.counters["tangent_modular_power_exponent_bits"] = (
        result.ledger.counters.get("tangent_modular_power_exponent_bits", 0)
        + result.returns.bit_length()
    )
    return data
