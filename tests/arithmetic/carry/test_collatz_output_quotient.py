"""Independent finite proofs of the raw quotient and its observation limits."""

from itertools import product

import pytest

from number_compiler.arithmetic.carry.collatz_carry_wires import (
    collatz_digit_carry_action,
    collatz_dyadic_carry_partition,
    compose_collatz_carry_actions,
)
from number_compiler.arithmetic.carry.collatz_output_quotient import (
    CORRECTIONS,
    DOMAIN_ACTIONS,
    RADIX64_DIRECTIONAL_DOMAIN_COUNTS,
    RADIX64_DIRECTIONAL_DOMAIN_TABLES,
    RADIX64_DIRECTIONAL_VALUE_COUNTS,
    RADIX64_LEFT_VIEW_CLASSES,
    RADIX64_RIGHT_VIEW_CLASSES,
    RAW_CLASS_STARTS,
    radix64_correction,
    radix64_domain,
    radix64_domain_from_directional_views,
    radix64_geometry_emit,
    radix64_growth_edge,
    radix64_join_shift_views,
    radix64_left_domain_view,
    radix64_raw_class,
    radix64_raw_emit,
    radix64_right_domain_view,
    radix64_shift,
    radix64_shift_views,
    radix64_value_potential,
)


def _action(digit: int) -> tuple[int, ...]:
    return tuple((3 * digit + c) // 64 for c in range(3))


def test_generic_dyadic_carry_consumer_owns_both_orientations() -> None:
    expected_counts = (1, 2, 4, 5, 5, 5, 5)
    for bits, expected_count in enumerate(expected_counts):
        base = 1 << bits
        actions, classes = collatz_dyadic_carry_partition(bits)
        assert len(actions) == expected_count
        assert len(classes) == base
        for value in range(base):
            assert actions[classes[value]] == tuple(
                (3 * value + carry) // base for carry in range(3)
            )
    for shift in range(1, 6):
        assert RADIX64_LEFT_VIEW_CLASSES[shift] is RADIX64_RIGHT_VIEW_CLASSES[6 - shift]
    for shift in range(6):
        left_actions, left_classes = collatz_dyadic_carry_partition(6 - shift)
        right_actions, right_classes = collatz_dyadic_carry_partition(shift)
        for quotient, remainder in product(range(64 >> shift), range(1 << shift)):
            composed = compose_collatz_carry_actions(
                right_actions[right_classes[remainder]],
                left_actions[left_classes[quotient]],
            )
            joined = radix64_join_shift_views(quotient, remainder, shift)
            assert composed == collatz_digit_carry_action(joined, base=64)
            assert (
                DOMAIN_ACTIONS[
                    RADIX64_DIRECTIONAL_DOMAIN_TABLES[shift][left_classes[quotient]][
                        right_classes[remainder]
                    ]
                ]
                == composed
            )


def test_seventeen_classes_are_exactly_the_declared_observation_partition() -> None:
    signatures = [
        (
            _action(d),
            tuple(((3 * d + c) // 64, _action((3 * d + c) % 64)) for c in range(3)),
        )
        for d in range(64)
    ]
    assert len(set(signatures)) == 17
    for a, b in product(range(64), repeat=2):
        assert (radix64_raw_class(a) == radix64_raw_class(b)) == (
            signatures[a] == signatures[b]
        )
    for d, c in product(range(64), range(3)):
        k, p = radix64_raw_class(d), radix64_value_potential(d)
        outgoing, raw = radix64_raw_emit(k, p, c)
        assert (outgoing, raw) == divmod(3 * d + c, 64)
        assert raw == 3 * d + radix64_correction(c, outgoing)
        assert raw == radix64_raw_emit(k, 0, c)[1] + 3 * p
        assert radix64_geometry_emit(d, c) == (outgoing, raw)
    assert {
        radix64_correction(c, out) for c, out in product(range(3), repeat=2)
    } == set(CORRECTIONS)
    assert max(radix64_value_potential(d) for d in range(64)) == 6


def test_old_eq_dies_in_raw_output_but_other_inputs_can_create_raw_eq() -> None:
    for d, c in product((21, 42), range(3)):
        _, raw = radix64_raw_emit(radix64_raw_class(d), 0, c)
        assert radix64_domain(raw) in (0, 4)
    _, born = radix64_raw_emit(radix64_raw_class(7), 0, 0)
    assert born == 21 and radix64_domain(born) == 1


def test_shift_wiring_and_restricted_growth_exhaustively() -> None:
    for raw, adjacent, e in product(range(64), range(64), range(6)):
        assert radix64_shift(raw, adjacent, e) == ((raw + 64 * adjacent) >> e) % 64
        quotient, _ = radix64_shift_views(raw, e)
        _, remainder = radix64_shift_views(adjacent, e)
        assert radix64_join_shift_views(quotient, remainder, e) == radix64_shift(
            raw, adjacent, e
        )
        left = radix64_left_domain_view(raw, e)
        right = radix64_right_domain_view(adjacent, e)
        assert radix64_domain_from_directional_views(left, right, e) == radix64_domain(
            radix64_shift(raw, adjacent, e)
        )
    for c, e in product(range(3), range(6)):
        edge = radix64_growth_edge(c, e)
        assert edge == c // 2**e
        assert not edge or radix64_domain(edge) == 0
        if e >= 2:
            assert edge == 0


def test_directional_domain_views_are_noninjective_and_cross_source_domains() -> None:
    assert RADIX64_DIRECTIONAL_DOMAIN_COUNTS == (
        (5, 1),
        (5, 2),
        (5, 4),
        (5, 5),
        (4, 5),
        (2, 5),
    )
    assert RADIX64_DIRECTIONAL_VALUE_COUNTS == (5, 10, 20, 25, 20, 10)
    for shift in range(6):
        left, right = (
            RADIX64_LEFT_VIEW_CLASSES[shift],
            RADIX64_RIGHT_VIEW_CLASSES[shift],
        )
        assert len(left) == 64 >> shift
        assert len(right) == 1 << shift
        assert left == tuple(sorted(left))
        assert right == tuple(sorted(right))
    mixed_counts = []
    value_counts = []
    for shift in range(6):
        # The current domain has already supplied the carry.  It is deliberately
        # absent from the resulting value-view identity.
        for carry in range(3):
            fibers: dict[tuple[int, int], list[int]] = {}
            for digit in range(64):
                raw = (3 * digit + carry) % 64
                key = (
                    radix64_left_domain_view(raw, shift),
                    radix64_right_domain_view(raw, shift),
                )
                fibers.setdefault(key, []).append(digit)
            value_counts.append(len(fibers))
            mixed_counts.append(
                sum(
                    len({radix64_domain(digit) for digit in fiber}) > 1
                    for fiber in fibers.values()
                )
            )
    assert value_counts[::3] == [5, 10, 20, 25, 20, 10]
    assert len(set(value_counts[0:3])) == 1
    assert len(set(value_counts[3:6])) == 1
    assert len(set(value_counts[6:9])) == 1
    assert len(set(value_counts[9:12])) == 1
    assert len(set(value_counts[12:15])) == 1
    assert len(set(value_counts[15:18])) == 1
    assert mixed_counts[::3] == [3, 6, 12, 21, 12, 6]


def test_raw_class_cannot_replace_value_at_a_shift_seam() -> None:
    assert radix64_raw_class(0) == radix64_raw_class(5)
    a = radix64_raw_emit(radix64_raw_class(0), 0, 1)[1]
    b = radix64_raw_emit(radix64_raw_class(5), 5, 1)[1]
    assert (a, b) == (1, 16)
    assert (radix64_shift(a, 21, 3), radix64_shift(b, 21, 3)) == (40, 42)
    assert radix64_domain(40) != radix64_domain(42)


def test_invalid_classes_potentials_and_phases_fail_closed() -> None:
    for k in range(17):
        stop = RAW_CLASS_STARTS[k + 1] if k < 16 else 64
        with pytest.raises(ValueError):
            radix64_raw_emit(k, stop - RAW_CLASS_STARTS[k], 0)
    for e in (-1, 6):
        with pytest.raises(ValueError):
            radix64_shift(0, 0, e)
        with pytest.raises(ValueError):
            radix64_shift_views(0, e)
        with pytest.raises(ValueError):
            radix64_left_domain_view(0, e)
    with pytest.raises(ValueError):
        radix64_join_shift_views(64, 0, 0)
    with pytest.raises(ValueError):
        radix64_join_shift_views(0, 1, 0)
    with pytest.raises(ValueError):
        radix64_domain_from_directional_views(5, 0, 0)
    with pytest.raises(TypeError):
        radix64_raw_class(True)
    with pytest.raises(TypeError):
        radix64_raw_emit(0, 0, True)
    with pytest.raises(TypeError):
        radix64_geometry_emit(0, True)
    with pytest.raises(TypeError):
        collatz_dyadic_carry_partition(True)
    with pytest.raises(ValueError):
        collatz_dyadic_carry_partition(17)
    with pytest.raises(ValueError):
        collatz_digit_carry_action(2, base=2)
    with pytest.raises(ValueError):
        compose_collatz_carry_actions((0, 1, 3), (0, 1, 2))
