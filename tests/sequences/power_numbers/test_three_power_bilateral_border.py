"""Bilateral low-binary/decimal -> conditional middle -> radial-high audit."""

from itertools import product

import pytest

from number_compiler.arithmetic.carry.tripling_transfer import (
    IDENTITY,
    compose_transfer,
    digit_transfer,
    unknown_middle_transfer_set,
)
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
    RadixBilateralTripling,
    carry_h5,
)


def _digits_lsd(value: int, base: int) -> list[int]:
    digits = []
    while value:
        digits.append(value % base)
        value //= base
    return digits or [0]


def _true_middle_transfer(
    source: int, radix: RadixBilateralTripling
) -> tuple[int, int, int]:
    digits = _digits_lsd(source, radix.base)
    middle = digits[radix.low_places : -radix.high_places]
    assert len(middle) == radix.unknown_middle_length
    action = IDENTITY
    for digit in middle:
        action = compose_transfer(action, digit_transfer(radix.base, digit))
    return action


def test_exact_middle_set_powers_without_enumerating_digits() -> None:
    for base in (2, 10):
        for length in range(4):
            brute = set()
            for digits in product(range(base), repeat=length):
                result = IDENTITY
                for digit in digits:
                    result = compose_transfer(result, digit_transfer(base, digit))
                brute.add(result)
            assert unknown_middle_transfer_set(base, length) == brute
        assert len(unknown_middle_transfer_set(base, 10**12)) <= 27


def test_radial_leading_decimal_and_binary_are_certified() -> None:
    with GrowthArithmeticEvaluator(
        ResourceLedger(), max_work_units=25_000_000
    ) as evaluator:
        for exponent in (2, 4, 8, 16, 64, 128, 256, 512):
            for base in (2, 10):
                radial = RadialSturmianClock(HomogeneousGrowthScale(exponent, 0))
                order = evaluator.radix_order(radial.scale, base)
                width = min(4, order + 1)
                packet = radial.leading_radix(evaluator, base, width)
                expected_digits = _digits_lsd(3**exponent, base)
                assert packet.word_length == len(expected_digits)
                actual = 0
                for d in expected_digits[-width:][::-1]:
                    actual = actual * base + d
                assert packet.value == actual


def test_real_ordinary_tripling_both_sides_sound() -> None:
    for level in range(3, 8):
        packet = FermatNumberSpec(4).demand_three_power_bilateral_border(
            level,
            low_binary_places=3,
            low_decimal_places=1,
            high_binary_places=3,
            high_decimal_places=1,
        )
        source = 3 ** (1 << level)  # Audit truth only, never used by demand.
        for border in (packet.binary, packet.decimal):
            true_fn = _true_middle_transfer(source, border)
            assert true_fn in border.allowed_middle_actions
            assert true_fn[border.low_carry] in border.high_ingress_options
            # Independently check the printed low and high source/target.
            b = border.base
            lower_power = b**border.low_places
            assert border.low_source == source % lower_power
            assert border.low_product == (3 * source) % lower_power
            assert border.low_carry == (3 * (source % lower_power)) // lower_power
            assert border.source_top == source // b ** (
                border.source_digits - border.high_places
            )
            target = 3 * source
            assert border.target_top == target // b ** (
                border.target_digits - border.high_places
            )
            assert border.terminal_status == "UNKNOWN"
            assert not border.middle_h5_authenticated


def test_h5_from_both_sides_filters_short_missing_middle() -> None:
    packet = FermatNumberSpec(4).demand_three_power_bilateral_border(
        3,
        low_binary_places=3,
        high_binary_places=3,
        low_decimal_places=1,
        high_decimal_places=1,
    )
    source = 3**8
    for border in (packet.binary, packet.decimal):
        digits = _digits_lsd(source, border.base)
        carry = 0
        carries = []
        for digit in digits:
            carry = (3 * digit + carry) // border.base
            carries.append(carry)
        # Only a full separately checked harmonic may refine the middle.
        h5 = carry_h5(tuple(carries), 0)
        filtered = border.condition_on_full_h5(h5)
        assert filtered
        assert _true_middle_transfer(source, border) in filtered
        assert len(filtered) <= len(border.allowed_middle_actions)
        assert (
            border.condition_on_full_h5((carry_h5(tuple(carries), 0)[0], h5[1]))
            == filtered
        )
        with pytest.raises(ValueError, match="precision-budget"):
            FermatNumberSpec(4).demand_three_power_bilateral_border(
                14
            ).decimal.condition_on_full_h5(h5)


def test_terminal_f4_f5_are_constrained_but_not_classified() -> None:
    for n, t in ((4, 14), (4, 15), (5, 30), (5, 31)):
        packet = FermatNumberSpec(n).demand_three_power_bilateral_border(t)
        assert packet.binary.high_forgets_ingress
        assert packet.decimal.high_forgets_ingress
        assert packet.binary.producer_verified and packet.decimal.producer_verified
        assert packet.terminal_status == "UNKNOWN"
        for b in (packet.binary, packet.decimal):
            assert b.allowed_middle_actions
            assert b.unknown_middle_length > 1000
            assert b.high_h5_options
            assert b.low_h5 == carry_h5(b.low_carry_vector, 0)
        if n == 4 and t == 14:
            assert packet.decimal.forced_middle_action == (2, 2, 2)
        if n == 4 and t == 15:
            assert packet.decimal.forced_middle_action == (0, 0, 0)
        if n == 5 and t == 30:
            assert packet.decimal.forced_high_ingress == 1
            assert len(packet.decimal.allowed_middle_actions) == 2
        if n == 5 and t == 31:
            assert packet.decimal.forced_middle_action is None


def test_bilateral_does_not_treat_dyadic_step_as_ordinary_tripling() -> None:
    # X_2=81 -> X_3=6561 gives 81 -> 61 modulo 100; ordinary
    # tripling gives 81 -> 43. The two clocks are different.
    assert (3**4) % 100 == 81
    assert (3**8) % 100 == 61
    assert (3 * 3**4) % 100 == 43
    packet = FermatNumberSpec(4).demand_three_power_bilateral_border(
        2,
        low_binary_places=2,
        high_binary_places=2,
        low_decimal_places=1,
        high_decimal_places=1,
    )
    assert packet.decimal.low_product == 3 * 81 % 10


def test_adaptive_unit_counter_feeds_bilateral_binary_and_decimal_ports() -> None:
    # The same normalized unit source authenticates the binary source islands
    # used by the two-sided decimal/binary carry and radial packet.
    for n, t in ((4, 14), (5, 30)):
        adaptive = FermatNumberSpec(n).demand_adaptive_three_power_interior(
            t, ((0, 128), (500, 16), (1024, 12))
        )
        refined = adaptive.bilateral_source_constraints(
            decimal_windows=((12, 4), (60, 4)),
        )
        assert refined.terminal_status == "UNKNOWN"
        assert refined.binary_middle.source_authenticated
        assert refined.decimal_middle.source_authenticated
        assert not refined.binary_middle.complete_source
        assert len(refined.binary_middle.windows) == len(adaptive.windows)
        assert [item.radix_value for item in refined.binary_middle.windows] == [
            item.source_bits for item in adaptive.windows
        ]
        assert set(refined.binary_middle.possible_actions).issubset(
            adaptive.bilateral_source_constraints().bilateral.binary.allowed_middle_actions
        )
        assert len(refined.decimal_middle.possible_actions) <= len(
            refined.bilateral.decimal.allowed_middle_actions
        )


def test_exact_low_decimal_dyadic_orbit_is_not_tripling_step() -> None:
    source = [pow(3, 1 << t, 100) for t in range(2, 8)]
    assert source == [81, 61, 21, 41, 81, 61]
    # The ordinary 3X carry emitting at each low boundary is separate.
    ordinary = [(3 * s // 100, (3 * s) % 100) for s in source]
    assert ordinary[:4] == [(2, 43), (1, 83), (0, 63), (1, 23)]


def test_81_61_100_boundary_carries_are_retained_inside_low_prefix() -> None:
    for index, levels in ((4, (14, 15)), (5, (30, 31))):
        source_port = FermatNumberSpec(index)
        samples = tuple(
            source_port.demand_three_power_bilateral_border(t).decimal for t in levels
        )
        assert tuple(p.low_source % 100 for p in samples) == (81, 61)
        assert tuple(p.low_carry_vector[1] for p in samples) == (2, 1)
        assert tuple(p.low_carry_vector[-1] for p in samples) == tuple(
            p.low_carry for p in samples
        )


@pytest.mark.parametrize("kind", ["copy", "alias", "nested"])
def test_bilateral_border_requires_original_producer(kind: str) -> None:
    from dataclasses import replace

    from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
        refine_middle_source_windows,
    )

    border = FermatNumberSpec(4).demand_three_power_bilateral_border(14).decimal
    if kind == "copy":
        border = replace(border)
    elif kind == "alias":
        object.__setattr__(border, "level", 14.0)
    else:
        object.__setattr__(border.low_h5[0], "phi2", 99)
    assert not border.producer_verified
    with pytest.raises(TypeError, match="authenticated"):
        refine_middle_source_windows(border, ())
