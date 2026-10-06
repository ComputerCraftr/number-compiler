"""Differentials for shared active-width extrema and chronological composition."""

from itertools import product

import pytest

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger


def literal_walk(steps: tuple[int, ...]) -> BlankLedger:
    position = 0
    positions = [position]
    for step in steps:
        position += step
        positions.append(position)
    return BlankLedger(position, min(positions), max(positions))


def test_split_walks_preserve_extrema_and_order() -> None:
    for steps in product((-2, 0, 3), repeat=4):
        expected = literal_walk(steps)
        for split in range(5):
            assert (
                literal_walk(steps[:split]).then(literal_walk(steps[split:]))
                == expected
            )
    rise, fall = literal_walk((3,)), literal_walk((-2,))
    assert rise.then(fall) != fall.then(rise)


@pytest.mark.parametrize("steps", [(), (3, -2), (-3, 1), (2, -2), (-2, 0, 3)])
def test_repetition_matches_literal_walk(steps: tuple[int, ...]) -> None:
    summary = literal_walk(steps)
    for copies in range(9):
        assert summary.repeat(copies) == literal_walk(steps * copies)


def test_huge_repetition_uses_closed_prefix_formula() -> None:
    copies = 10**30
    assert BlankLedger(1, -2, 3).repeat(copies) == BlankLedger(copies, -2, copies + 2)
    assert BlankLedger(-1, -3, 2).repeat(copies) == BlankLedger(-copies, -copies - 2, 2)


@pytest.mark.parametrize("values", [(1, 0, 0), (-1, 0, 0), (0, 1, 1), (0, -1, -1)])
def test_extrema_include_initial_and_final_width(values: tuple[int, int, int]) -> None:
    with pytest.raises(ValueError):
        BlankLedger(*values)


def test_invalid_types_and_repeat_counts_are_rejected() -> None:
    with pytest.raises(TypeError):
        BlankLedger(True)
    with pytest.raises(ValueError):
        BlankLedger().repeat(True)
    with pytest.raises(ValueError):
        BlankLedger().repeat(-1)
