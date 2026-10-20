from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.interfaces.diamond_boundary import (
    ContinuationStep,
    ImageBinding,
)
from tests.support.assertions import assert_rejected_atomically
from tests.support.diamond_boundary import boundary, composed_anchor


def test_constant_reduction_preserves_domain_and_codomain_admissibility() -> None:
    ledger, actions, _, arena, first, second = boundary()
    output = arena.literal(second, 0, 0)
    function = arena.constant(output, first, 1)
    size = arena.domain_size(first, 1)
    assert size is not None
    assert arena.finite_function([output] * size, first, 1) == function
    assert arena.select(function, arena.literal(first, 1, 0)) == output
    other = arena.constant(output, actions.identity, 1)
    assert other != function
    wrong_side = arena.literal(first, 0, 0)
    wrong_action = arena.literal(second, 1, 0)
    before = ledger.snapshot()
    for argument in (wrong_side, wrong_action):
        with pytest.raises(ValueError, match="another continuation domain"):
            arena.select(function, argument)
    assert ledger.snapshot() == before


def test_primitive_literals_and_foreign_handles_fail_before_publication() -> None:
    ledger, actions, _, arena, first, _ = boundary()
    _, other_actions, _, other, foreign, _ = boundary()
    arena.literal(first, 0, 0)
    before = ledger.snapshot()
    for action, side, value in (
        (first, 0, 1 << 80),
        (first, True, 0),
        (foreign, 0, 0),
        (actions.identity, 0, 1),
    ):
        with pytest.raises(ValueError):
            arena.literal(action, side, value)
    with pytest.raises(ValueError):
        arena.constant(other.literal(other_actions.identity, 0, 0), first, 1)
    assert ledger.snapshot() == before


def test_pair_requires_exact_first_opposite_to_second_same_interface() -> None:
    ledger, actions, _, arena, first, second = boundary()
    composed, anchor = composed_anchor(actions, arena, first, second)
    output = arena.literal(second, 0, 0)
    correct = arena.constant(output, first, 1)
    wrong = arena.constant(output, first, 0)
    result = arena.pair(composed, 0, anchor, correct)
    assert arena.state(result).continuation == correct
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="wrong interface"):
        arena.pair(composed, 0, anchor, wrong)
    with pytest.raises(ValueError, match="composed action"):
        arena.pair(first, 0, anchor, correct)
    assert ledger.snapshot() == before


def test_substitution_validates_provider_and_foreign_action_before_warm_hit() -> None:
    ledger, actions, cells, arena, first, second = boundary()
    _, _, _, _, foreign, _ = boundary()
    left = arena.literal(actions.identity, 0, 0)
    right = arena.literal(actions.identity, 1, 0)
    provider = ImageBinding(actions.identity, cells.source(0, 2), left, right)
    previous = arena.constant(arena.literal(second, 0, 0), first, 1)
    step = ContinuationStep(
        first, second, 0, previous, provider, arena.literal(first, 0, 0)
    )
    result = arena.substitution(step)
    assert arena.action(result).step == step
    before = ledger.snapshot()
    with pytest.raises(ValueError):
        arena.substitution(replace(step, first=foreign))
    with pytest.raises(ValueError, match="image ports"):
        arena.substitution(replace(step, provider=replace(provider, left=right)))
    assert ledger.snapshot() == before


def test_complete_finite_function_validates_all_values_and_reserves_atomically() -> (
    None
):
    ledger, actions, _, arena, first, second = boundary()
    size = arena.domain_size(first, 1)
    assert size is not None and size > 1
    values = [arena.literal(second, 0, index % 2) for index in range(size)]
    ledger.max_cache_entries = ledger.entries + 1
    before = assert_rejected_atomically(
        ledger,
        lambda: arena.finite_function(values, first, 1),
        BlockContextBudgetExceeded,
    )
    with pytest.raises(ValueError, match="complete primitive"):
        arena.finite_function(values[:-1], first, 1)
    assert ledger.snapshot() == before
    ledger.max_cache_entries = None
    function = arena.finite_function(values, first, 1)
    for index, expected in enumerate(values):
        assert arena.select(function, arena.literal(first, 1, index)) == expected
    composed = actions.compose(first, second)
    before = assert_rejected_atomically(
        ledger,
        lambda: arena.finite_function(values, composed, 1),
        ValueError,
        match="complete primitive",
    )
