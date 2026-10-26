"""First-event height and p-adic regressions from comma Entry arithmetic."""

from __future__ import annotations

import pytest

from tests.sequences.comma.event_height_oracle import (
    affine_quotient_mod,
    completed_height_mod_prime_power,
    cycle,
    direct_first_event,
    event,
    event_control_observation,
    finite_event_periods,
    height_mod_prime_power,
    ordered_children,
    signature,
    source_mod_prime_power,
)
from tests.sequences.comma.padic_event_oracle import is_prime, valuation


def test_exact_signed_affine_inspection_height() -> None:
    result = event(1, 83, 6)
    assert (result.cycle_length, result.cycle_displacement) == (10, 460)
    assert result.selected_headroom == 337
    assert result.near_steps == 5
    assert result.terminal_headroom == 82
    assert result.kind == "fork"
    assert result.affine_numerator_constant == -1_900
    assert result.cycle_displacement * result.event_height == (
        result.cycle_length * 10**result.width + result.affine_numerator_constant
    )
    assert result.event_height == 21_735
    assert result.completed_height == result.event_height
    assert valuation(result.event_height, 3) == 3


@pytest.mark.parametrize(
    ("leading", "offset", "width"),
    [(1, 0, 5), (1, 83, 5), (4, 17, 5), (9, 0, 5), (9, 3, 5)],
)
def test_default_literal_event_representatives(
    leading: int, offset: int, width: int
) -> None:
    observed = event(leading, offset, width)
    assert direct_first_event(leading, offset, width) == (
        observed.event_height,
        observed.source_integer,
        observed.kind,
    )


@pytest.mark.parametrize(
    ("kind", "leading", "offset", "width", "v_at_width", "v_next"),
    [
        ("fork", 1, 83, 6, 3, 4),
        ("sector_cross", 1, 0, 35, 4, 3),
        ("landmine", 9, 3, 49, 0, 4),
        ("decade_cross", 9, 0, 9, 3, 0),
    ],
)
def test_same_phase_inspection_height_valuation_witnesses(
    kind: str,
    leading: int,
    offset: int,
    width: int,
    v_at_width: int,
    v_next: int,
) -> None:
    first = event(leading, offset, width)
    second = event(leading, offset, width + 924)
    assert first.kind == second.kind == kind
    assert event_control_observation(leading, offset, width) == (
        event_control_observation(leading, offset, width + 924)
    )
    assert first.selected_headroom == second.selected_headroom
    assert first.terminal_headroom == second.terminal_headroom
    assert first.near_steps == second.near_steps
    assert first.affine_numerator_constant == second.affine_numerator_constant
    assert valuation(first.event_height, 3) == v_at_width
    assert valuation(second.event_height, 3) == v_next
    assert valuation(first.event_height, 3) != valuation(second.event_height, 3)
    if kind in ("sector_cross", "decade_cross"):
        assert first.completed_height == first.event_height + 1
        assert second.completed_height == second.event_height + 1
    else:
        assert first.completed_height == first.event_height
        assert second.completed_height == second.event_height


@pytest.mark.parametrize(
    ("kind", "leading", "offset", "width", "v_at_width", "v_next", "headroom"),
    [
        ("sector_cross", 1, 0, 36, 4, 3, 11),
        ("decade_cross", 9, 0, 11, 0, 2, 91),
    ],
)
def test_same_phase_completed_crossing_height_witnesses(
    kind: str,
    leading: int,
    offset: int,
    width: int,
    v_at_width: int,
    v_next: int,
    headroom: int,
) -> None:
    first = event(leading, offset, width)
    second = event(leading, offset, width + 924)
    assert first.kind == second.kind == kind
    assert first.terminal_headroom == second.terminal_headroom == headroom
    assert first.near_steps == second.near_steps
    assert first.event_height != first.completed_height
    assert second.event_height != second.completed_height
    first_completed_constant = (
        first.affine_numerator_constant + first.cycle_displacement
    )
    second_completed_constant = (
        second.affine_numerator_constant + second.cycle_displacement
    )
    assert first.cycle_displacement * first.completed_height == (
        first.cycle_length * 10**first.width + first_completed_constant
    )
    assert second.cycle_displacement * second.completed_height == (
        second.cycle_length * 10**second.width + second_completed_constant
    )
    assert valuation(first.completed_height, 3) == v_at_width
    assert valuation(second.completed_height, 3) == v_next
    assert valuation(first.completed_height, 3) != valuation(second.completed_height, 3)


@pytest.mark.parametrize(
    ("kind", "leading", "offset", "width", "v_at_width", "v_next", "headroom"),
    [
        ("decade_cross", 9, 3, 8, 4, 3, 1),
        ("landmine", 9, 10, 7, 4, 3, 73),
    ],
)
def test_same_phase_terminal_source_integer_valuation_witnesses(
    kind: str,
    leading: int,
    offset: int,
    width: int,
    v_at_width: int,
    v_next: int,
    headroom: int,
) -> None:
    first = event(leading, offset, width)
    second = event(leading, offset, width + 924)
    assert first.kind == second.kind == kind
    assert first.terminal_headroom == second.terminal_headroom == headroom
    assert valuation(first.source_integer, 3) == v_at_width
    assert valuation(second.source_integer, 3) == v_next
    if headroom == 1:
        assert valuation(first.source_integer, 3) == 2 + valuation(width + 1, 3)
        assert valuation(second.source_integer, 3) == 2 + valuation(width + 925, 3)


def test_ordered_fork_children_keep_width_dependent_2_and_5_adic_values() -> None:
    for width in (6, 930, 13, 937):
        result = event(1, 83 if width in (6, 930) else 2, width)
        assert result.kind == "fork"
        near_child, exact_boundary_child = ordered_children(result)
        scale = 10**width
        assert (near_child, exact_boundary_child) == (2 * scale - 1, 2 * scale)
        assert near_child == result.source_integer + 10 * result.event_digit + 1
        assert exact_boundary_child == near_child + 1
        for prime in (2, 5):
            assert valuation(near_child, prime) == 0
            assert valuation(exact_boundary_child, prime) == (
                width + valuation(2, prime)
            )


def test_exact_9_to_1_power_of_ten_child_across_widths() -> None:
    for width in (5, 929):
        result = event(9, 0, width)
        assert result.kind == "decade_cross"
        assert result.terminal_headroom == 91
        assert result.event_digit == 9
        (next_value,) = ordered_children(result)
        assert next_value == result.source_integer + 10 * result.event_digit + 1
        assert next_value == 10 ** (width + 1)
        assert valuation(next_value, 2) == width + 1
        assert valuation(next_value, 5) == width + 1


def test_modular_height_path_handles_huge_width_without_building_power() -> None:
    leading, offset, prime, level = 1, 83, 3, 4
    width = 6 + 924 * 1_000_000
    height_period, source_period = finite_event_periods(leading, offset, prime, level)
    assert height_period == source_period == 2_772
    assert signature(leading, offset, width)[-1] == -1_900
    assert signature(leading, offset, 1_000_000_000)[-1] != -1_900
    assert event_control_observation(leading, offset, width) != (
        event_control_observation(leading, offset, 1_000_000_000)
    )
    assert height_mod_prime_power(leading, offset, width, prime, level) == (
        height_mod_prime_power(leading, offset, width + height_period, prime, level)
    )
    assert completed_height_mod_prime_power(
        leading, offset, width, prime, level
    ) == completed_height_mod_prime_power(
        leading, offset, width + height_period, prime, level
    )
    assert source_mod_prime_power(leading, offset, width, prime, level) == (
        source_mod_prime_power(leading, offset, width + source_period, prime, level)
    )


def test_height_period_includes_displacement_valuation_separately_from_source() -> None:
    leading, offset, prime, level = 7, 0, 13, 1
    displacement = cycle(leading, offset % 10)[1]
    assert displacement == 520
    assert valuation(displacement, prime) == 1
    height_period, source_period = finite_event_periods(leading, offset, prime, level)
    assert height_period == 12_012
    assert source_period == 924
    assert height_period > source_period
    assert height_mod_prime_power(
        leading, offset, 5, prime, level
    ) == height_mod_prime_power(leading, offset, 5 + height_period, prime, level)
    assert source_mod_prime_power(
        leading, offset, 5, prime, level
    ) == source_mod_prime_power(leading, offset, 5 + source_period, prime, level)


def test_generic_affine_2_and_5_valuations_with_and_without_constant() -> None:
    # The bounded canonical Entry scan found no actual comma C=0 case. These
    # C=0 checks are explicitly generic affine arithmetic, not source claims.
    for width in (5, 7, 20):
        quotient_two = (10**width + 8) // 8
        assert affine_quotient_mod(1, 8, 8, width, 2, 8) == quotient_two % 2**8
        assert valuation(quotient_two, 2) == 0

        quotient_five = (10**width + 25) // 25
        assert affine_quotient_mod(1, 25, 25, width, 5, 8) == quotient_five % 5**8
        assert valuation(quotient_five, 5) == 0

        zero_constant = 10**width // 8
        assert affine_quotient_mod(1, 8, 0, width, 2, 8) == zero_constant % 2**8
        assert valuation(zero_constant, 2) == width - 3
        assert valuation(zero_constant, 5) == width


def test_generic_nonzero_constant_valuations_stabilize_after_divisibility() -> None:
    # Once w exceeds v_p(P), these signed nonzero constants give stable
    # valuations. These are generic affine examples, not admitted comma rows.
    for width in range(5, 11):
        quotient_two = (10**width - 8) // 8
        quotient_five = (10**width - 25) // 25
        assert valuation(quotient_two, 2) == 0
        assert valuation(quotient_five, 5) == 0
        assert affine_quotient_mod(1, 8, -8, width, 2, 8) == quotient_two % 2**8
        assert affine_quotient_mod(1, 25, -25, width, 5, 8) == quotient_five % 5**8


@pytest.mark.validation
def test_all_855_width_five_entries_match_literal_first_event_walk() -> None:
    comparisons = 0
    for leading in range(1, 10):
        for offset in range(90 + leading):
            observed = event(leading, offset, 5)
            assert direct_first_event(leading, offset, 5) == (
                observed.event_height,
                observed.source_integer,
                observed.kind,
            )
            comparisons += 1
    assert comparisons == 855


@pytest.mark.validation
def test_480_finite_level_period_checks_for_each_height_and_source_channel() -> None:
    height_checks = completed_checks = source_checks = 0
    cases = ((1, 0), (1, 83), (4, 17), (7, 2), (9, 0), (9, 3))
    for prime in (3, 7, 11, 23, 29):
        for level in range(1, 5):
            for leading, offset in cases:
                height_period, source_period = finite_event_periods(
                    leading, offset, prime, level
                )
                for width in (5, 7, 9, 15):
                    assert height_mod_prime_power(
                        leading, offset, width, prime, level
                    ) == height_mod_prime_power(
                        leading, offset, width + height_period, prime, level
                    )
                    height_checks += 1
                    assert completed_height_mod_prime_power(
                        leading, offset, width, prime, level
                    ) == completed_height_mod_prime_power(
                        leading, offset, width + height_period, prime, level
                    )
                    completed_checks += 1
                    assert source_mod_prime_power(
                        leading, offset, width, prime, level
                    ) == source_mod_prime_power(
                        leading, offset, width + source_period, prime, level
                    )
                    source_checks += 1
    assert height_checks == completed_checks == source_checks == 480


def test_event_order_inputs_are_exact_primes_and_width_integers() -> None:
    assert is_prime(2) and is_prime(97)
    assert not is_prime(1) and not is_prime(91)
    with pytest.raises(TypeError, match="exact integer"):
        event(True, 0, 5)
    with pytest.raises(TypeError, match="exact integer"):
        event(1, False, 5)
    with pytest.raises(TypeError, match="exact integer"):
        height_mod_prime_power(1, 83, 5, True, 1)
