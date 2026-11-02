"""Finite controlled mod-7 action and exact carry-switch projection tests."""

from __future__ import annotations

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.sequences.reverse_add.punctured_temporal import (
    CarryPrefix,
    PuncturedTemporalWork,
)
from number_compiler.sequences.reverse_add.temporal_matrix7_port import (
    Mod7CarryPortAction,
    action_from_carry_switches,
    aligned_difference_mod7_from_switches,
)


def _reverse_decimal(value: int) -> int:
    result = 0
    while value:
        value, digit = divmod(value, 10)
        result = result * 10 + digit
    return result


def _pair_symbols(value: int) -> tuple[int, ...]:
    digits = digits_lsd(value, 10)
    return tuple(
        left + right for left, right in zip(digits, reversed(digits), strict=True)
    )


def _step(value: int) -> tuple[int, int, int, int]:
    width = len(digits_lsd(value, 10))
    following = value + _reverse_decimal(value)
    following_width = len(digits_lsd(following, 10))
    growth = following_width - width
    aligned_difference = following - _reverse_decimal(following) // (10**growth)
    return following, growth, aligned_difference, width


def test_controlled_affine_monoid_has_21_distinct_maps() -> None:
    generators = {
        Mod7CarryPortAction.from_port(difference_mod7=r, growth=growth)
        for growth in (0, 1)
        for r in range(7)
    }
    assert len(generators) == 14

    actions = {Mod7CarryPortAction.identity()}
    for _ in range(3):
        actions |= {
            earlier.then(later) for earlier in tuple(actions) for later in generators
        }

    assert actions == {
        Mod7CarryPortAction(multiplier, correction)
        for multiplier in (1, 2, 4)
        for correction in range(7)
    }
    assert len({tuple(action.apply(x) for x in range(7)) for action in actions}) == 21
    assert all(action.power(21) == Mod7CarryPortAction.identity() for action in actions)


def test_carry_switch_projection_matches_seed_196_exact_steps() -> None:
    source = 196
    composed = Mod7CarryPortAction.identity()
    initial_after_one, _, _, _ = _step(source)
    initial_action_input = initial_after_one % 7

    for _ in range(160):
        following, growth, difference, width = _step(source)
        work = PuncturedTemporalWork()
        prefix = CarryPrefix(
            tuple((symbol, 1) for symbol in _pair_symbols(source)), work
        )
        switches = prefix.switch_offsets()
        assert prefix.carry_at(width) == growth
        assert aligned_difference_mod7_from_switches(width, switches) == difference % 7
        action = action_from_carry_switches(width, switches)
        assert action == Mod7CarryPortAction.from_port(
            difference_mod7=difference % 7, growth=growth
        )
        next_following, _, _, _ = _step(following)
        assert action.apply(following % 7) == next_following % 7
        if following % 11 == 0:
            carry_mod7 = (difference - 3 * growth) % 7
            from_switches = (
                ((following % 77) // 11 - (3 * carry_mod7 + 1)) % 7
                if growth
                else -carry_mod7 % 7
            )
            exact_defect = (_reverse_decimal(following) - following) // 99
            from_residues = (
                (_reverse_decimal(following) % 693 - following % 693) % 693
            ) // 99
            assert from_switches == from_residues == exact_defect % 7
        composed = composed.then(action)
        assert composed.apply(initial_action_input) == next_following % 7
        source = following


def test_carry_switch_projection_handles_trillion_cell_rle_port() -> None:
    width = 10**12
    switches = (1,)
    expected = (3 + (pow(3, width - 1, 7) - 1) * 4) % 7
    assert aligned_difference_mod7_from_switches(width, switches) == expected
    assert action_from_carry_switches(width, switches) == (
        Mod7CarryPortAction.from_port(difference_mod7=expected, growth=1)
    )
