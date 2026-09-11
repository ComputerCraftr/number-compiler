from __future__ import annotations

from number_compiler.arithmetic.carry.carry_labels import (
    IDENTITY as I,
)
from number_compiler.arithmetic.carry.carry_labels import (
    RESET_ONE as R1,
)
from number_compiler.arithmetic.carry.carry_labels import (
    RESET_ZERO as R0,
)
from number_compiler.arithmetic.formula.formula import FormulaArena, root_from_values
from number_compiler.arithmetic.formula.summary import (
    compose_summaries,
    get_summary,
    summary_from_values,
)
from number_compiler.arithmetic.formula.types import RadixSpec


def test_seed_summary_is_compiler_metadata_not_state() -> None:
    arena = FormulaArena()
    spec = RadixSpec(10)
    root = root_from_values((9, 9, 12, 9, 9), arena, spec)
    summary = get_summary(arena, root, spec, required=True)
    assert summary.length == 5
    assert summary.first_reset == 2 == summary.last_reset
    assert summary.first_reset_sign == 1
    assert summary.transfer == R1
    assert summary.growth_from_outer_symmetry == 1
    assert set(root.__slots__) == {"planes"}


def test_summary_concatenation_is_constant_size_and_exact() -> None:
    spec = RadixSpec(10)
    left = summary_from_values((9, 9, 3), spec)
    right = summary_from_values((9, 14, 9), spec)
    both = compose_summaries(left, right)
    expected = summary_from_values((9, 9, 3, 9, 14, 9), spec)
    assert both == expected

    allp = summary_from_values((9, 9), spec)
    assert allp.transfer == I
    assert compose_summaries(allp, allp).all_threshold
    assert summary_from_values((3,), spec).transfer == R0


def test_event_selective_growth_does_not_regress_to_eager_full_prefix() -> None:
    from number_compiler.arithmetic.formula.derived import successor

    arena = FormulaArena()
    spec = RadixSpec(10)
    root = root_from_values((7, 18, 7), arena, spec)
    for _ in range(100):
        root = successor(arena, root, spec)
    # The 196 prefix has an outer effective reset almost immediately.  This is
    # an instrumentation tripwire: the old eager evaluator exceeded 108k closed
    # bit evaluations here; true AND/OR short-circuiting is comfortably below it.
    assert arena.metadata_counter("summary_selective_positions") <= 220
    assert arena.cached_closed_bits < 80_000
