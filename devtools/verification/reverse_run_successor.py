"""Counted-run positive control for the exact reverse/add successor.

This is an explicit reference endpoint representation, not a runtime future
ID or a powered quotient. Work is proportional to run boundaries, independent
of run lengths. Arithmetic and carry actions use the production local owners.
"""

from __future__ import annotations

import json
from collections.abc import Sequence

from devtools.verification import exact_oracle, require_exact_oracle
from number_compiler.arithmetic.carry.carry_monoid import apply_carry_fn
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.radix import reverse_pair_sums, symbol_runs
from number_compiler.arithmetic.fields.run_pairing import pair_mirror_digit_runs
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_normalized_coordinates,
    decimal_pair_carry_action,
)

Runs = tuple[tuple[int, int], ...]


def _append(out: list[tuple[int, int]], symbol: int, count: int) -> None:
    """Coalesce a counted block without visiting its represented cells."""
    if count == 0:
        return
    if out and out[-1][0] == symbol:
        out[-1] = symbol, out[-1][1] + count
    else:
        out.append((symbol, count))


def _admit(source: Runs) -> None:
    if type(source) is not tuple or not source:
        raise ValueError("nonempty immutable pair runs required")
    previous = -1
    for item in source:
        if type(item) is not tuple or len(item) != 2:
            raise ValueError("run requires a symbol and positive count")
        symbol, count = item
        if (
            type(symbol) is not int
            or not 0 <= symbol <= 18
            or type(count) is not int
            or count <= 0
            or symbol == previous
        ):
            raise ValueError("pair runs must be valid and coalesced")
        previous = symbol
    if source != source[::-1]:
        raise ValueError("pair runs must represent a symmetric field")


def run_successor(source: Runs) -> tuple[Runs, int]:
    """Normalize counted blocks and align with their reversed digit blocks.

    Each carry action is idempotent. Only the first cell of a run can differ
    from the remaining cells; EQ preserves the carry from preceding domains.
    The growth digit participates in reversal just like every other digit.
    No loop iterates over a run count, and no carry track is constructed.
    """
    require_exact_oracle()
    _admit(source)
    digits: list[tuple[int, int]] = []
    carry = 0
    for symbol, count in source:
        alpha, beta = decimal_normalized_coordinates(symbol, carry)
        _append(digits, alpha + 5 * beta, 1)
        carry = apply_carry_fn(decimal_pair_carry_action(symbol), carry)
        if count > 1:
            alpha, beta = decimal_normalized_coordinates(symbol, carry)
            _append(digits, alpha + 5 * beta, count - 1)
    if carry:
        _append(digits, 1, 1)
    result, _odd_width, _run_pair_visits = pair_mirror_digit_runs(
        digits, half_only=False
    )
    _admit(result)
    return result, carry


def compare_trajectory(seed: int, steps: int = 100) -> dict[str, object]:
    """Compare after each symbolic step, with expansion confined to the oracle."""
    require_exact_oracle()
    if type(seed) is not int or seed < 0 or not 0 <= steps <= 1000:
        raise ValueError((seed, steps))
    field = reverse_pair_sums(seed, 10)
    runs = symbol_runs(field)
    rows = []
    for event in range(1, steps + 1):
        runs, growth = run_successor(runs)
        field, oracle_growth = pair_step(field, 10)
        if growth != oracle_growth or runs != symbol_runs(field):
            raise AssertionError((seed, event, runs, field))
        if event in (1, 4, 10, 25, 50, 100, steps):
            rows.append({"event": event, "width": len(field), "runs": len(runs)})
    return {"seed": seed, "exact_steps": steps, "samples": rows}


def uniform_control(length: int) -> Sequence[Runs]:
    require_exact_oracle()
    if type(length) is not int or length <= 0:
        raise ValueError(length)
    runs: Runs = ((2, length),)
    rows: list[Runs] = [runs]
    for _ in range(4):
        runs, _growth = run_successor(runs)
        rows.append(runs)
    expected = ((7, 2),) if length == 1 else ((7, 1), (14, length - 1), (7, 1))
    if runs != expected:
        raise AssertionError((length, runs))
    return rows


def main() -> None:
    with exact_oracle():
        report = {
            "scope": "counted exact successor; no powered quotient admission",
            "million_width_control": uniform_control(1_000_000),
            "trajectories": [compare_trajectory(seed) for seed in (1, 1111, 196)],
        }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
