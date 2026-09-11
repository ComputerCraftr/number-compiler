"""Sequential nonbinary Collatz formula orbits used as exact proof oracles."""

from __future__ import annotations

from number_compiler.arithmetic.fields.digit_formula import (
    DigitSpec,
    closed_digit_at,
    digit_root_from_int,
    root_to_int,
)
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    formula_metrics,
)
from number_compiler.sequences.collatz.orbit import CollatzStep
from number_compiler.sequences.collatz.radix import (
    TERNARY,
    collatz_successor_formula_local_composite_radix,
    collatz_successor_formula_ternary,
)


def _record(
    rows: list[CollatzStep],
    arena: FormulaArena,
    spec: DigitSpec,
    index: int,
    branch: str,
    current: FormulaRoot,
    *,
    materialize_values: bool,
    transducer_states: int = 0,
    transition_monoid_size: int = 0,
) -> None:
    value = root_to_int(arena, current, spec) if materialize_values else None
    metrics = formula_metrics(current)
    rows.append(
        CollatzStep(
            index,
            branch,
            current,
            value,
            current.width,
            int(metrics["nodes"]),
            transducer_states,
            transition_monoid_size,
            (),
        )
    )


def collatz_orbit_formulas_ternary(
    seed: int,
    *,
    max_steps: int = 10000,
    stop_at_one: bool = True,
    materialize_values: bool = False,
) -> tuple[FormulaArena, tuple[CollatzStep, ...]]:
    seed, max_steps = int(seed), int(max_steps)
    if seed <= 0 or max_steps < 0:
        raise ValueError((seed, max_steps))
    arena = FormulaArena()
    root = digit_root_from_int(seed, arena, TERNARY)
    rows: list[CollatzStep] = []
    _record(
        rows, arena, TERNARY, 0, "seed", root, materialize_values=materialize_values
    )
    for index in range(max_steps):
        if stop_at_one and root.width == 1 and closed_digit_at(arena, root, 0) == 1:
            break
        root, branch, compiled = collatz_successor_formula_ternary(arena, root)
        _record(
            rows,
            arena,
            TERNARY,
            index + 1,
            branch,
            root,
            materialize_values=materialize_values,
            transducer_states=len(compiled.transducer.states),
            transition_monoid_size=compiled.monoid.size,
        )
    return arena, tuple(rows)


def collatz_orbit_formulas_local_composite_radix(
    seed: int,
    *,
    radix: int = 6,
    max_steps: int = 10000,
    stop_at_one: bool = True,
    materialize_values: bool = False,
) -> tuple[FormulaArena, tuple[CollatzStep, ...]]:
    seed, radix, max_steps = int(seed), int(radix), int(max_steps)
    if seed <= 0 or max_steps < 0 or radix < 2 or radix % 6:
        raise ValueError((seed, radix, max_steps))
    spec = DigitSpec(radix)
    arena = FormulaArena()
    root = digit_root_from_int(seed, arena, spec)
    rows: list[CollatzStep] = []
    _record(rows, arena, spec, 0, "seed", root, materialize_values=materialize_values)
    for index in range(max_steps):
        if stop_at_one and root.width == 1 and closed_digit_at(arena, root, 0) == 1:
            break
        root, branch, _compiled = collatz_successor_formula_local_composite_radix(
            arena, root, spec
        )
        _record(
            rows,
            arena,
            spec,
            index + 1,
            branch,
            root,
            materialize_values=materialize_values,
        )
    return arena, tuple(rows)


__all__ = [
    "collatz_orbit_formulas_local_composite_radix",
    "collatz_orbit_formulas_ternary",
]
