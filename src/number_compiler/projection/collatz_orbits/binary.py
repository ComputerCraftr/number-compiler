"""Exact whole-orbit Collatz formula oracle.

This module deliberately owns the sequential reference traversal.  Powered
point, width, and radix queries use the recursive field-image runtime instead.
"""

from __future__ import annotations

from collections.abc import Iterable

from number_compiler.arithmetic.fields.digit_formula import (
    CompiledDigitTransduction,
    closed_digit_at,
    digit_root_from_int,
    root_to_int,
)
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    formula_metrics,
)
from number_compiler.resources.instrumentation import ResidueChannel, residue_bundle
from number_compiler.sequences.collatz.orbit import (
    BINARY,
    CollatzStep,
    collatz_successor_formula,
)


def collatz_orbit_formulas(
    seed: int,
    *,
    max_steps: int = 10000,
    stop_at_one: bool = True,
    materialize_values: bool = False,
    channels: Iterable[ResidueChannel] = (),
) -> tuple[FormulaArena, tuple[CollatzStep, ...]]:
    """Generate the exact sequential formula orbit for proof and compatibility."""
    seed = int(seed)
    if seed <= 0:
        raise ValueError("Collatz seed must be positive")
    max_steps = int(max_steps)
    if max_steps < 0:
        raise ValueError(max_steps)
    ch = tuple(channels)
    arena = FormulaArena()
    root = digit_root_from_int(seed, arena, BINARY)
    rows: list[CollatzStep] = []

    def record(
        index: int,
        branch: str,
        current: FormulaRoot,
        comp: CompiledDigitTransduction | None = None,
    ) -> None:
        value = root_to_int(arena, current, BINARY) if materialize_values else None
        fm = formula_metrics(current)
        residues = (
            tuple(
                (z, m, r)
                for (z, m), r in residue_bundle(arena, current, BINARY, ch).items()
            )
            if ch
            else ()
        )
        if comp is None:
            tstates = 0
            msize = 0
        else:
            tstates = len(comp.transducer.states)
            msize = comp.monoid.size
        rows.append(
            CollatzStep(
                index,
                branch,
                current,
                value,
                current.width,
                int(fm["nodes"]),
                tstates,
                msize,
                residues,
            )
        )

    record(0, "seed", root)
    for k in range(max_steps):
        if stop_at_one and root.width == 1 and closed_digit_at(arena, root, 0) == 1:
            break
        root, branch, compiled = collatz_successor_formula(arena, root)
        record(k + 1, branch, root, compiled)
    return arena, tuple(rows)


def collatz_values(seed: int, max_steps: int = 10000) -> tuple[int, ...]:
    """Materialize the exact reference orbit values explicitly."""
    _arena, rows = collatz_orbit_formulas(
        seed, max_steps=max_steps, stop_at_one=True, materialize_values=True
    )
    return tuple(int(row.value) for row in rows if row.value is not None)


__all__ = ["collatz_orbit_formulas", "collatz_values"]
