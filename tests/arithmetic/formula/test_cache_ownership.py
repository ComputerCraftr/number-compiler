"""Colliding arena-local IDs must never authorize formula cache reuse."""

from __future__ import annotations

from collections.abc import Callable

import pytest

from number_compiler.arithmetic.carry.prefix_monoid import (
    compile_formula_prefix_predicate,
)
from number_compiler.arithmetic.fields.digit_formula import (
    DigitSpec,
    DigitTransducer,
    compile_digit_transducer,
    digit_value_masks,
)
from number_compiler.arithmetic.formula.derived import carry_out
from number_compiler.arithmetic.formula.event_formula import carry_event_formula_view
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    canonical_root_key,
    root_from_values,
)
from number_compiler.arithmetic.formula.pair_algebra import carry_prefix_projection
from number_compiler.arithmetic.formula.smb_formula import smb_formula_view
from number_compiler.arithmetic.formula.summary import get_summary
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.sequences.reverse_add.digits import next_digit_formula


def test_closed_bit_cache_rejects_foreign_local_id_before_lookup() -> None:
    arena, foreign = FormulaArena(), FormulaArena()
    zero, one = arena.literal(0, 1), foreign.literal(1, 1)
    assert zero.id == one.id
    assert arena.eval_closed_bit(zero, 0) == 0
    before = arena.cached_closed_bits
    with pytest.raises(ValueError, match="another arena"):
        arena.eval_closed_bit(one, 0)
    assert arena.cached_closed_bits == before
    assert arena.eval_closed_bit(zero, 0) == 0
    assert foreign.eval_closed_bit(one, 0) == 1


FormulaQuery = Callable[[FormulaArena, FormulaRoot], object]
_PAIR = RadixSpec(2)
_DIGIT = DigitSpec(3)
_IDENTITY = DigitTransducer(3, (0,), 0, {(0, d): (0, d) for d in range(3)})


@pytest.mark.parametrize(
    "query",
    (
        lambda a, r: get_summary(a, r, _PAIR, required=True),
        lambda a, r: carry_out(a, r, _PAIR),
        lambda a, r: carry_prefix_projection(a, r.planes, _PAIR),
        lambda a, r: smb_formula_view(a, r, _PAIR),
        lambda a, r: carry_event_formula_view(a, r, _PAIR),
        lambda a, r: next_digit_formula(a, r, _PAIR),
        lambda a, r: digit_value_masks(a, r, _DIGIT),
        lambda a, r: compile_digit_transducer(a, r, _DIGIT, _IDENTITY),
        lambda a, r: compile_formula_prefix_predicate(a, r.planes[0]),
    ),
    ids=(
        "summary",
        "carry",
        "carry-prefix",
        "smb",
        "event",
        "digits",
        "masks",
        "transducer",
        "predicate",
    ),
)
def test_warm_formula_views_reject_foreign_root_with_colliding_ids(
    query: FormulaQuery,
) -> None:
    arena, foreign = FormulaArena(), FormulaArena()
    root = root_from_values((1, 1, 1), arena, _PAIR)
    other = root_from_values((2, 2, 2), foreign, _PAIR)
    assert canonical_root_key(root) == canonical_root_key(other)
    query(arena, root)
    before = (arena.node_count, dict(arena._metadata), dict(arena._derived))
    with pytest.raises(ValueError, match="another arena"):
        query(arena, other)
    assert (arena.node_count, arena._metadata, arena._derived) == before
    query(arena, root)


@pytest.mark.parametrize("operation", ("and_", "or_", "xor", "ite"))
def test_boolean_simplification_cannot_alias_foreign_ids(operation: str) -> None:
    arena, foreign = FormulaArena(), FormulaArena()
    local, other = arena.literal(0, 2), foreign.literal(3, 2)
    assert local.id == other.id
    before = arena.node_count
    with pytest.raises(ValueError, match="another arena"):
        if operation == "ite":
            arena.ite(local, local, other)
        else:
            getattr(arena, operation)(local, other)
    assert arena.node_count == before
