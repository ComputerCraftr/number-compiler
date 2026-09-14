from __future__ import annotations

import itertools

from number_compiler.arithmetic.fields.digit_formula import (
    DigitSpec,
    digit_root_from_int,
    root_to_int,
)
from number_compiler.arithmetic.formula.formula import FormulaArena
from number_compiler.sequences.collatz.radix import (
    collatz_orbit_formulas_local_composite_radix,
    collatz_successor_formula_local_composite_radix,
)


def _step(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def test_local_composite_radix_collatz_exact_in_base6_and12() -> None:
    for base in (6, 12):
        for seed in (1, 3, 7, 27, 97):
            _arena, rows = collatz_orbit_formulas_local_composite_radix(
                seed, radix=base, max_steps=160, materialize_values=True
            )
            values = []
            for row in rows:
                assert row.value is not None
                values.append(row.value)
            for a, b in itertools.pairwise(values):
                assert b == _step(a)
            assert values[-1] == 1


def test_local_base6_step_uses_no_prefix_transducer_state() -> None:
    spec = DigitSpec(6)
    arena = FormulaArena()
    root = digit_root_from_int(27, arena, spec)
    out, branch, compiled = collatz_successor_formula_local_composite_radix(
        arena, root, spec
    )
    assert compiled is None
    assert branch == "multiply_3_add_1_local"
    assert root_to_int(arena, out, spec) == 82
