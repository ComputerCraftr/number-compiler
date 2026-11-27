"""Checked five- and six-column source actions retain exact ordered clips."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    append_decimal_value,
)
from number_compiler.sequences.antihydra import mahler_cf_reciprocal_tile as tiles
from number_compiler.sequences.antihydra.mahler_cf_low_period import settled_low_action


def _literal(value: int, width: int) -> Matrix2:
    return Matrix2(append_decimal_value(value, 10 ** (width - 1), (1, 0, 0, 1)))


@pytest.mark.parametrize("width", (5, 6))
def test_five_six_phase_actions_are_complete_ordered_operators(width: int) -> None:
    period = 1 << (width - 2)
    first = [settled_low_action(width + phase, width) for phase in range(period)]
    assert len(set(first)) == period
    for exponent in range(width, width + 2 * period):
        action = settled_low_action(exponent, width)
        expected = _literal(int.__pow__(5, exponent, 10**width), width)
        assert action == expected.entries
        assert settled_low_action(exponent + period, width) is action
        # Both surrounding products retain their own chronological order.
        left = Matrix2.digit(2)
        right = Matrix2.digit(9)
        assert left.multiply(Matrix2(action)).multiply(right) == left.multiply(
            expected
        ).multiply(right)


def test_short_settled_selection_does_not_import_phase56() -> None:
    source = Path(__file__).resolve().parents[3] / "src"
    program = """\
import sys
sys.path.insert(0, sys.argv[1])
from number_compiler.sequences.antihydra.mahler_cf_low_period import settled_low_action
settled_low_action(3,2)
settled_low_action(7,4)
assert 'number_compiler.sequences.antihydra.mahler_cf_low_phase56' not in sys.modules
"""
    subprocess.run([sys.executable, "-I", "-c", program, str(source)], check=True)


def test_reciprocal_physical_suffix_is_selected_before_digit_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[tuple[int, int, int]] = []
    original = tiles.reciprocal_row_interval

    def guarded(q: int, t: int, width: int, start: int, count: int) -> int:
        calls.append((width, start, count))
        assert start + count <= width - min(width, 6)
        return original(q, t, width, start, count)

    monkeypatch.setattr(tiles, "reciprocal_row_interval", guarded)
    observed: set[int] = set()
    for exponent in range(6, 20):
        value = 5**exponent
        width = len(str(value))
        tile = tiles.ReciprocalTile(value, (width,), 0, width, exponent)
        observed.add(min(width, 6))
        assert tile.product == _literal(value, width)
        for start in range(max(0, width - 6), width):
            count = width - start
            assert tile.segment(start, count) == _literal(value % 10**count, count)
    assert {5, 6} <= observed
    assert calls
