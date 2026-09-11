"""Sequential sentinel-coordinate Collatz orbits for proof and diagnostics."""

from __future__ import annotations

from number_compiler.arithmetic.fields.digit_formula import (
    DigitSpec,
    digit_root_from_int,
    root_to_int,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.formula.formula import FormulaArena, formula_metrics
from number_compiler.sequences.collatz.raw_field import (
    CollatzSentinelFormulaStep,
    CollatzSentinelStep,
    accelerated_collatz_sentinel_formula_step,
    accelerated_collatz_sentinel_step_digits,
    power4_radix_bits,
)


def collatz_sentinel_orbit(
    seed: int, *, base: int = 16, max_odd_steps: int = 10000
) -> tuple[CollatzSentinelStep, ...]:
    seed, max_odd_steps = int(seed), int(max_odd_steps)
    if seed <= 0 or max_odd_steps < 0:
        raise ValueError((seed, max_odd_steps))
    while seed > 1 and not (seed & 1):
        seed >>= 1
    digits = tuple(digits_lsd(seed, int(base)))
    out: list[CollatzSentinelStep] = []
    for _index in range(max_odd_steps):
        if digits == (1,):
            break
        step = accelerated_collatz_sentinel_step_digits(digits, base=int(base))
        out.append(step)
        digits = step.target_digits
    return tuple(out)


def collatz_orbit_formulas_sentinel_power4(
    seed: int,
    *,
    radix: int = 4,
    max_odd_steps: int = 10000,
    materialize_values: bool = False,
) -> tuple[FormulaArena, tuple[CollatzSentinelFormulaStep, ...]]:
    seed, radix, max_odd_steps = int(seed), int(radix), int(max_odd_steps)
    if seed <= 0 or max_odd_steps < 0:
        raise ValueError((seed, max_odd_steps))
    power4_radix_bits(radix)
    while seed > 1 and not (seed & 1):
        seed >>= 1
    spec = DigitSpec(radix)
    arena = FormulaArena()
    root = digit_root_from_int(seed, arena, spec)
    rows: list[CollatzSentinelFormulaStep] = []

    def record(index: int, valuation: int, stripped: int, local: int) -> None:
        metrics = formula_metrics(root)
        rows.append(
            CollatzSentinelFormulaStep(
                index,
                valuation,
                stripped,
                local,
                root,
                int(metrics["nodes"]),
                int(metrics["description_bits"]),
            )
        )

    record(0, 0, 0, 0)
    for index in range(1, max_odd_steps + 1):
        if root.width == 1 and root_to_int(arena, root, spec) == 1:
            break
        root, valuation, stripped, local = accelerated_collatz_sentinel_formula_step(
            arena, root, base=radix
        )
        if materialize_values:
            root_to_int(arena, root, spec)
        record(index, valuation, stripped, local)
    return arena, tuple(rows)


__all__ = ["collatz_orbit_formulas_sentinel_power4", "collatz_sentinel_orbit"]
