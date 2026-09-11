from __future__ import annotations

import itertools

from number_compiler.arithmetic.carry.event_memory import carry_field
from number_compiler.arithmetic.functions.state_reduction import (
    CollatzValuationState,
    ReverseAddGrowthState,
)


def _palindrome(half: tuple[int, ...], width: int) -> tuple[int, ...]:
    half = tuple(half)
    return half + tuple(reversed(half[: width // 2]))


def test_reverse_growth_state_is_exact_for_exhaustive_symmetric_pair_fields() -> None:
    for base in range(3, 8):
        for width in range(1, 7):
            half = (width + 1) // 2
            for values in itertools.product(range(2 * base - 1), repeat=half):
                pair = _palindrome(values, width)
                reduced = ReverseAddGrowthState.from_pair(pair, base=base)
                assert reduced.growth == carry_field(pair, base=base)[-1]
                assert reduced.description_bits < 4 * width + 32


def test_reverse_growth_boundary_is_position_plus_signed_residual_not_carry_word() -> (
    None
):
    state = ReverseAddGrowthState.from_pair((9, 9, 12, 9, 9), base=10)
    assert (state.boundary_offset, state.boundary_relation, state.growth) == (2, 1, 1)
    state = ReverseAddGrowthState.from_pair((9, 7, 18, 7, 9), base=10)
    assert (state.boundary_offset, state.boundary_relation, state.growth) == (1, -1, 0)
    state = ReverseAddGrowthState.from_pair((9, 9, 9), base=10)
    assert state.all_neutral and state.growth == 0


def test_collatz_valuation_state_is_exact_action_and_shift_phase() -> None:
    for value in range(1, 4096, 2):
        state = CollatzValuationState.from_odd_value(value)
        target = (3 * value + 1) >> state.valuation
        assert state.apply(value) == target
        assert state.increases == (target > value)
        for order in (1, 2, 3, 4, 5, 8, 13):
            assert state.shift_phase(order) == state.valuation % order
        assert state.projection.odd_steps == 1
        assert state.projection.valuation_sum == state.valuation


def test_collatz_valuation_state_is_not_mislabeled_closed() -> None:
    # k=1 occurs at both sources, but the next accelerated valuation differs.
    found: dict[tuple[object, ...], tuple[object, ...]] = {}
    conflict = None
    for value in range(1, 20000, 2):
        current = CollatzValuationState.from_odd_value(value)
        nxt_value = current.apply(value)
        nxt = CollatzValuationState.from_odd_value(nxt_value)
        old = found.get(current.canonical_key)
        if old is not None and old != nxt.canonical_key:
            conflict = (value, current, nxt)
            break
        found[current.canonical_key] = nxt.canonical_key
    assert conflict is not None
