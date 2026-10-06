from __future__ import annotations

import itertools

from number_compiler.arithmetic.carry.event_memory import carry_field
from number_compiler.arithmetic.functions.state_reduction import ReverseAddGrowthState


def _palindrome(half: tuple[int, ...], width: int) -> tuple[int, ...]:
    half = tuple(half)
    return half + tuple(reversed(half[: width // 2]))


def test_reverse_growth_boundary_is_position_plus_signed_residual_not_carry_word() -> (
    None
):
    state = ReverseAddGrowthState.from_pair((9, 9, 12, 9, 9), base=10)
    assert (state.boundary_offset, state.boundary_relation, state.growth) == (2, 1, 1)
    state = ReverseAddGrowthState.from_pair((9, 7, 18, 7, 9), base=10)
    assert (state.boundary_offset, state.boundary_relation, state.growth) == (1, -1, 0)
    state = ReverseAddGrowthState.from_pair((9, 9, 9), base=10)
    assert state.all_neutral and state.growth == 0


def test_reverse_growth_state_is_exact_for_exhaustive_symmetric_pair_fields() -> None:
    for base in range(3, 8):
        for width in range(1, 7):
            half = (width + 1) // 2
            for values in itertools.product(range(2 * base - 1), repeat=half):
                pair = _palindrome(values, width)
                reduced = ReverseAddGrowthState.from_pair(pair, base=base)
                assert reduced.growth == carry_field(pair, base=base)[-1]
                assert reduced.description_bits < 4 * width + 32
