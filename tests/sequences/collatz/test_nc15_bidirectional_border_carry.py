"""Exact upper/lower carry bridge for source-selected 6305 returns."""

from __future__ import annotations

from number_compiler.sequences.collatz.border_carry_cylinder import (
    Border6305CarryCylinder,
    next_6305_upper_numerator,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    select_border_return_macro,
)


def _v2(value: int) -> int:
    return (value & -value).bit_length() - 1


def test_three_ending_carry_cylinder_matches_exact_return_and_lifts() -> None:
    for source in range(3, 20_003, 10):
        cursor = Border6305CarryCylinder.from_three_digit(source)
        q = (source - 3) // 10
        numerator = 3 * q + 1
        exponent = _v2(numerator)
        upper_odd = numerator >> exponent
        endpoint = (15 * upper_odd + 1) // 2

        assert cursor.upper_numerator == numerator
        assert cursor.zero_tail == exponent
        assert cursor.upper_odd == upper_odd
        assert cursor.endpoint == endpoint
        assert 3 * source + 1 == 10 * numerator
        assert endpoint == ((9 * source) >> (exponent + 2)) + (
            2 if exponent == 0 else 1
        )
        assert endpoint % 5 == 3
        assert cursor.endpoint_digit == endpoint % 10
        assert cursor.endpoint_residue20 == endpoint % 20

        for upper_bits in (1, 2, 3, 5):
            residue, modulus = cursor.source_congruence(upper_bits)
            assert source % modulus == residue
            if upper_bits > 1:
                previous, previous_modulus = cursor.source_congruence(upper_bits - 1)
                assert modulus == 2 * previous_modulus
                assert residue % previous_modulus == previous

        following = cursor.next_return()
        if upper_odd % 4 == 3:
            assert following is not None
            assert following.upper_numerator == (9 * upper_odd + 1) // 4
            assert following.zero_tail == _v2(9 * upper_odd + 1) - 2
            assert next_6305_upper_numerator(upper_odd) == following.upper_numerator
        else:
            assert following is None
            assert upper_odd % 8 in (1, 5)


def test_hot_selector_preserves_physical_and_normalized_clocks() -> None:
    for source, ticks, tails, endpoint in (
        (13, 7, (2,), 4),
        (23, 13, (0, 4), 4),
        (33, 5, (1,), 38),
        (43, 7, (0,), 74),
    ):
        macro = select_border_return_macro(source, ticks)
        assert macro is not None
        assert macro.zero_tails == tails
        assert macro.endpoint == endpoint
        assert macro.physical_ticks == ticks
        assert macro.return_physical_ticks == tuple(j + 4 for j in tails)
        assert macro.return_normalized_steps == tuple(j + 2 for j in tails)
        observation = macro.observation()
        assert observation["return_forced_decimal_carry"] == {
            "source_units": 3,
            "product_units": 0,
            "carry_into_next_decimal_position": 1,
        }
        assert observation["return_radial_scale"] == {
            "growths": 2 * len(tails),
            "halvings": sum(tails) + 2 * len(tails),
            "scope": "completed 6305 returns; entry and exit are separate",
        }


def test_three_border_successor_requires_the_exact_upper_return_port() -> None:
    # A source cylinder identifies finite low digits. It does not make an
    # 8-ending exit into a future 3-border return.
    returning = Border6305CarryCylinder.from_three_digit(23)
    exiting = Border6305CarryCylinder.from_three_digit(13)
    assert returning.endpoint == 53
    assert returning.next_return() is not None
    assert exiting.endpoint == 8
    assert exiting.next_return() is None


def test_zero_tail_free_count_is_only_the_exact_selected_prefix() -> None:
    for initial in range(1, 20_000, 2):
        current = initial
        expected = 0
        while current % 4 == 3:
            expected += 1
            current = (9 * current + 1) // 4
        cursor = Border6305CarryCylinder(initial)
        assert cursor.zero_tail_free_return_count == expected
