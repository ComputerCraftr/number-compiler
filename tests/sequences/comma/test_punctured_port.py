"""Independent local/physical references for the punctured comma port."""

from __future__ import annotations

from collections import Counter
from collections.abc import Callable
from math import gcd

import pytest

from number_compiler.sequences.comma import arithmetic
from number_compiler.sequences.comma.arithmetic import (
    classify_near_port,
    punctured_digit_port,
)


def _literal_near_prefix(leading: int, headroom: int) -> tuple[int, int]:
    count = 0
    while True:
        digit = (-headroom) % 10
        increment = 10 * digit + leading
        if headroom <= increment + int(leading < 9):
            return count, headroom
        headroom -= increment
        count += 1


def _literal_diagonal_pump(
    leading: int, digit: int, residual: int
) -> tuple[int, int, int]:
    count = 0
    while True:
        count += 1
        residual += 10
        gap = 10 * digit + leading
        if residual < gap:
            continue
        residual -= gap
        digit = (digit - leading) % 10
        if not digit:
            gap = 10 * digit + leading
            assert residual >= gap
            residual -= gap
            digit = (digit - leading) % 10
        return count, digit, residual


@pytest.mark.parametrize("leading", range(1, 10))
def test_port_locator_matches_all_bounded_physical_near_sources(leading: int) -> None:
    for headroom in range(1 + int(leading < 9), 541):
        result = classify_near_port(leading, headroom)
        assert (
            result.physical_steps,
            result.terminal_headroom,
        ) == _literal_near_prefix(leading, headroom)
        assert result.active_digit == (-result.terminal_headroom) % 10
        port = punctured_digit_port(leading, result.active_digit)
        assert 0 <= result.occurrence_row < port.dwell
        assert 1 <= result.port_visits <= 9


def test_all_81_ports_and_450_diagonal_occurrences_refine_local_rows() -> None:
    ports = 0
    occurrences = 0
    for leading in range(1, 10):
        for digit in range(1, 10):
            port = punctured_digit_port(leading, digit)
            ports += 1
            for row in range(port.dwell):
                residual = port.point_germ + 10 * row
                assert residual < 10 * digit + leading
                count, next_digit, next_residual = _literal_diagonal_pump(
                    leading, digit, residual
                )
                assert count == port.dwell - row
                assert next_digit == port.next_digit
                assert (
                    next_residual
                    == punctured_digit_port(leading, next_digit).point_germ
                )
                occurrences += 1
    assert ports == 81
    assert occurrences == 450


def test_punctured_weighted_cycles_recover_the_17_period_moduli() -> None:
    expected = {
        1: [46],
        2: [21, 26],
        3: [48],
        4: [22, 27],
        5: [6, 8, 10, 12, 14],
        6: [23, 28],
        7: [52],
        8: [24, 29],
        9: [54],
    }
    lengths: Counter[int] = Counter()
    for leading in range(1, 10):
        unseen = set(range(1, 10))
        weights = []
        while unseen:
            start = min(unseen)
            digit = start
            weight = length = 0
            while digit in unseen:
                unseen.remove(digit)
                port = punctured_digit_port(leading, digit)
                weight += port.dwell
                length += 1
                digit = port.next_digit
            assert digit == start
            weights.append(weight)
            lengths[length] += 1
        assert len(weights) == gcd(leading, 10)
        assert sorted(weights) == expected[leading]
    assert lengths == {9: 4, 5: 4, 4: 4, 2: 4, 1: 1}
    all_weights = [weight for weights in expected.values() for weight in weights]
    assert len(all_weights) == len(set(all_weights)) == 17


def test_classifier_uses_the_proved_canonical_cycle_seed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = arithmetic.punctured_digit_port
    calls: list[tuple[int, int]] = []

    def observed(
        leading: int,
        digit: int,
        *,
        charge_work: Callable[[int], None] | None = None,
        charge_bits: Callable[[int], None] | None = None,
    ) -> arithmetic.PuncturedDigitPort:
        calls.append((leading, digit))
        return original(
            leading, digit, charge_work=charge_work, charge_bits=charge_bits
        )

    monkeypatch.setattr(arithmetic, "punctured_digit_port", observed)
    for leading in range(1, 10):
        for digit in range(10):
            calls.clear()
            result = classify_near_port(leading, 1000 - digit)
            assert calls[0] == (
                leading,
                10 - leading + digit % gcd(leading, 10),
            )
            assert (result.physical_steps, result.terminal_headroom) == (
                _literal_near_prefix(leading, 1000 - digit)
            )


@pytest.mark.parametrize("leading", range(1, 10))
def test_raw_pair_field_recovers_sector_and_preserves_zero_root(leading: int) -> None:
    encodings: set[tuple[int, int]] = set()
    for digit in range(1, 10):
        previous = (digit - leading) % 10
        total, difference = digit + previous, digit - previous
        encodings.add((total, difference))
        assert (total + difference) // 2 == digit
        assert (total - difference) // 2 == previous
        assert difference % 10 == leading
        assert (10 * digit + leading) + (10 * previous + leading) == (
            10 * total + 2 * leading
        )
        if digit == leading:
            assert previous == 0
            port = punctured_digit_port(leading, digit)
            assert port.next_digit == 10 - leading
            assert _literal_diagonal_pump(leading, digit, port.point_germ)[1:] == (
                port.next_digit,
                punctured_digit_port(leading, port.next_digit).point_germ,
            )
    assert len(encodings) == 9


def test_puncture_keeps_the_zero_digit_as_the_second_adjacent_root() -> None:
    port = punctured_digit_port(1, 1)
    assert (port.point_germ, port.dwell, port.next_digit) == (3, 1, 9)
    # The punctured successor skips zero, but crossing its root still costs 1.
    # Replacing that gap by 10*next_digit+f would report only one crossing.
    assert _literal_diagonal_pump(1, 1, 3) == (1, 9, 1)
    z = port.point_germ + 10
    first_gap = 10 * port.digit + port.leading
    raw_previous = (port.digit - port.leading) % 10
    second_gap = 10 * raw_previous + port.leading
    assert (first_gap, second_gap) == (11, 1)
    assert z - first_gap - second_gap == 1
    assert z < first_gap + 10 * port.next_digit + port.leading


def test_diagonal_dwell_is_not_literal_physical_time() -> None:
    result = classify_near_port(1, 460)
    assert result.physical_steps == 9
    assert result.terminal_headroom == 91
    assert result.active_digit == 9
    assert 460 - (10 * ((-460) % 10) + 1) == 459
    assert classify_near_port(1, 459).physical_steps == 8
    # The first physical digit is zero; the arithmetic diagonal's active
    # port is a different chart, and its dwell must not become a TM weight.
    assert (-460) % 10 == 0
    assert punctured_digit_port(1, 9).dwell == 9


def test_huge_near_prefix_is_bounded_and_charged_without_scalar_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("weighted port classifier called a scalar endpoint oracle")

    monkeypatch.setattr(arithmetic, "_decimal_scale", forbidden)
    monkeypatch.setattr(arithmetic, "_sector_child_increments", forbidden)
    for headroom in (10**1000 + 123, 10**1000 + 124):
        work: list[int] = []
        bits: list[int] = []
        result = classify_near_port(
            7, headroom, charge_work=work.append, charge_bits=bits.append
        )
        assert 1 <= result.port_visits <= 9
        assert result.whole_cycles > 0
        assert sum(work) < 64
        assert sum(bits) > headroom.bit_length()
        assert (
            headroom
            - arithmetic.phase_prefix_displacement(
                7, (-headroom) % 10, result.physical_steps
            )
            == result.terminal_headroom
        )
        repeated_work: list[int] = []
        assert (
            classify_near_port(7, headroom, charge_work=repeated_work.append) == result
        )
        assert repeated_work == work


@pytest.mark.parametrize(
    "leading,digit", [(True, 1), (1, True), (0, 1), (10, 1), (1, 0), (1, 10)]
)
def test_port_rejects_noncanonical_coordinates(leading: int, digit: int) -> None:
    with pytest.raises(ValueError, match="punctured digit port"):
        punctured_digit_port(leading, digit)


@pytest.mark.parametrize(
    "leading,headroom",
    [(True, 7), (1, True), (0, 10), (10, 10), (1, 0), (1, 1), (9, 0)],
)
def test_locator_rejects_invalid_or_immediate_boundary_sources(
    leading: int, headroom: int
) -> None:
    with pytest.raises(ValueError, match="Near port source"):
        classify_near_port(leading, headroom)


def test_nine_weighted_cycle_signatures_remain_distinct() -> None:
    expected = {
        1: ((9, 46),),
        2: ((4, 21), (5, 26)),
        3: ((9, 48),),
        4: ((4, 22), (5, 27)),
        5: ((1, 6), (2, 8), (2, 10), (2, 12), (2, 14)),
        6: ((4, 23), (5, 28)),
        7: ((9, 52),),
        8: ((4, 24), (5, 29)),
        9: ((9, 54),),
    }
    signatures = []
    for leading in range(1, 10):
        unseen = set(range(1, 10))
        cycles = []
        while unseen:
            digit = start = min(unseen)
            length = weight = 0
            while digit in unseen:
                unseen.remove(digit)
                port = punctured_digit_port(leading, digit)
                length += 1
                weight += port.dwell
                digit = port.next_digit
            assert digit == start
            cycles.append((length, weight))
        signature = tuple(sorted(cycles))
        assert signature == expected[leading]
        signatures.append(signature)
    # Reflection shares unweighted control only. Distinct total weights cannot
    # be erased by relabeling states or by telescoping coboundary potentials.
    assert len(set(signatures)) == 9


def test_normalized_dwell_successor_seed_and_reset_match_all_81_ports() -> None:
    checked = 0
    for leading in range(1, 10):
        divisor = gcd(leading, 10)
        length = 10 // divisor
        step = leading // divisor
        for digit in range(1, 10):
            orbit, normalized = digit % divisor, digit // divisor
            epsilon = int(orbit == divisor - 1)
            port = punctured_digit_port(leading, digit)
            assert port.dwell == (
                orbit
                + divisor * normalized
                + (normalized + step + epsilon) // length
                - int(leading < 9 and orbit == divisor - 1 and normalized == length - 1)
            )
            assert port.dwell == digit + (digit + leading + 1) // 10 - int(
                leading < 9 and digit == 9
            )
            previous = (normalized + length - step) % length
            next_normalized = (
                (previous + length - step) % length
                if orbit == 0 and previous == 0
                else previous
            )
            assert port.next_digit == orbit + divisor * next_normalized
            seed = 10 - leading + orbit
            assert (seed - orbit) // divisor == length - step
            if leading < 9 and digit == 9:
                assert port.point_germ + 10 * port.dwell - (10 * digit + leading) == 0
            checked += 1
    assert checked == 81


def test_all_450_weighted_rows_keep_both_interval_bounds_and_source_headroom() -> None:
    checked = 0
    for leading in range(1, 10):
        divisor = gcd(leading, 10)
        length = 10 // divisor
        step = leading // divisor
        for orbit in range(divisor):
            seed = 10 - leading + orbit
            digit = seed
            states = []
            prefix = 0
            for _ in range(length - int(orbit == 0)):
                port = punctured_digit_port(leading, digit)
                states.append((port, prefix, prefix + port.dwell))
                prefix += port.dwell
                digit = port.next_digit
            assert digit == seed
            assert prefix == length * orbit + 5 * (length - 1) + step
            for row in range(prefix):
                # The signed Entry anchor reduces to H=10*W-o-10*row.
                # These are the actual Near sources for every weighted row.
                headroom = 10 * prefix - orbit - 10 * row
                result = classify_near_port(leading, headroom)
                selected, lower, upper = next(
                    state for state in states if row < state[2]
                )
                assert lower <= row < upper
                assert result.active_digit == selected.digit
                assert result.occurrence_row == row - lower
                assert result.occurrence_row < selected.dwell
                assert result.terminal_headroom == (
                    10 * selected.digit
                    + leading
                    + int(leading < 9)
                    - selected.point_germ
                    - 10 * (row - lower)
                )
                assert (result.physical_steps, result.terminal_headroom) == (
                    _literal_near_prefix(leading, headroom)
                )
                checked += 1
    assert checked == 450


def test_static_locator_catalog_covers_exact_weighted_intervals_and_is_optimal() -> (
    None
):
    total_comparisons = old_comparisons = 0
    expected_keys = {
        (leading, orbit)
        for leading in range(1, 10)
        for orbit in range(gcd(leading, 10))
    }
    assert set(arithmetic._PORT_LOCATORS) == expected_keys
    for leading, orbit in sorted(expected_keys):
        digit = seed = 10 - leading + orbit
        expected_leaves: list[tuple[int, int, int]] = []
        prefix = 0
        while not expected_leaves or digit != seed:
            port = punctured_digit_port(leading, digit)
            expected_leaves.append((-digit, prefix, prefix + port.dwell))
            prefix += port.dwell
            digit = port.next_digit
        tree = arithmetic._PORT_LOCATORS[leading, orbit]
        assert type(tree) is tuple
        visited = set()
        leaves = []

        pending = [(0, 0, prefix)]
        while pending:
            index, lower, upper = pending.pop()
            assert 0 <= index < len(tree)
            assert index not in visited
            visited.add(index)
            node = tree[index]
            assert type(node) is tuple
            assert len(node) == 3 and all(type(value) is int for value in node)
            split, left, right = node
            if split < 0:
                assert (left, right) == (lower, upper)
                assert lower < upper
                leaves.append(node)
            else:
                assert lower < split < upper
                pending.append((right, split, upper))
                pending.append((left, lower, split))

        assert len(visited) == len(tree)
        assert leaves == expected_leaves
        # Independently minimize weighted path length over all alphabetic
        # binary split positions. Leaf order and every physical dwell stay fixed.
        weights = [upper - lower for _, lower, upper in expected_leaves]
        costs: dict[tuple[int, int], int] = {}
        for size in range(1, len(weights) + 1):
            for lower in range(len(weights) - size + 1):
                upper = lower + size
                costs[lower, upper] = (
                    0
                    if size == 1
                    else sum(weights[lower:upper])
                    + min(
                        costs[lower, split] + costs[split, upper]
                        for split in range(lower + 1, upper)
                    )
                )
        orbit_comparisons = 0
        for row in range(prefix):
            node = tree[0]
            comparisons = 0
            while node[0] > 0:
                comparisons += 1
                node = tree[node[1] if row < node[0] else node[2]]
            headroom = 10 * prefix - orbit - 10 * row
            result = classify_near_port(leading, headroom)
            assert result.locator_comparisons == comparisons
            assert result.port_visits == 1
            assert (result.active_digit, result.occurrence_row) == (
                -node[0],
                row - node[1],
            )
            orbit_comparisons += comparisons
            old_comparisons += next(
                index + 1
                for index, (_, _, upper) in enumerate(expected_leaves)
                if row < upper
            )
        assert orbit_comparisons == costs[0, len(weights)]
        total_comparisons += orbit_comparisons
    assert old_comparisons == 1564
    assert total_comparisons == 1083


def test_runtime_constructs_only_canonical_and_selected_ports(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = arithmetic.punctured_digit_port
    calls = []

    def observed(
        leading: int,
        digit: int,
        *,
        charge_work: Callable[[int], None] | None = None,
        charge_bits: Callable[[int], None] | None = None,
    ) -> arithmetic.PuncturedDigitPort:
        calls.append((leading, digit))
        return original(
            leading, digit, charge_work=charge_work, charge_bits=charge_bits
        )

    monkeypatch.setattr(arithmetic, "punctured_digit_port", observed)
    for leading in range(1, 10):
        for headroom in range(1 + int(leading < 9), 541):
            calls.clear()
            work: list[int] = []
            result = classify_near_port(leading, headroom, charge_work=work.append)
            seed = 10 - leading + (-headroom) % gcd(leading, 10)
            expected = [(leading, seed)]
            if result.active_digit != seed:
                expected.append((leading, result.active_digit))
            assert calls == expected
            # Each decision is explicitly charged. The selected-leaf visit
            # does not hide comparisons, including the zero-comparison singleton.
            assert sum(work) >= result.locator_comparisons + len(calls)
