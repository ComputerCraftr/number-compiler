"""Exhaustive finite checks for the Collatz two-wire carry factorization."""

from __future__ import annotations

from itertools import product

import pytest

from number_compiler.arithmetic.carry.collatz_carry_wires import (
    CollatzCarryWires,
    collatz_digit_carry_wires,
)
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.sequences.collatz.pair import mul3_carry_monoid


@pytest.mark.parametrize("base", (4, 7, 10, 13, 16, 64, 256))
def test_digit_wires_equal_exact_three_state_carry(base: int) -> None:
    actions: set[tuple[int, int, int]] = set()
    for digit, carry in product(range(base), range(3)):
        action = collatz_digit_carry_wires(digit, base=base)
        actions.add(action.outputs)
        assert action.apply(carry) == (3 * digit + carry) // base
    closed_nonempty = {
        (0, 0, 0),
        (0, 1, 1),
        (1, 1, 1),
        (1, 1, 2),
        (2, 2, 2),
    }
    # Radix four obtains 111 by composing digit intervals; larger admitted
    # radices already contain it as a one-digit action.
    assert actions <= closed_nonempty
    assert {action.outputs for action in mul3_carry_monoid(base)} == closed_nonempty


@pytest.mark.parametrize("base", (4, 10, 16))
def test_two_wire_composition_matches_exhaustive_function_composition(
    base: int,
) -> None:
    actions = {collatz_digit_carry_wires(digit, base=base) for digit in range(base)}
    actions.add(CollatzCarryWires.identity())
    for after in actions:
        for before in actions:
            for carry in range(3):
                assert after.after(before).apply(carry) == after.apply(
                    before.apply(carry)
                )


def test_empty_identity_is_distinct_from_every_nonempty_digit_action() -> None:
    identity = CollatzCarryWires.identity()
    assert identity.outputs == (0, 1, 2)
    assert identity not in {collatz_digit_carry_wires(digit) for digit in range(10)}
    assert tuple(action.outputs for action in mul3_carry_monoid(10)) == (
        (0, 0, 0),
        (0, 1, 1),
        (1, 1, 1),
        (1, 1, 2),
        (2, 2, 2),
    )


@pytest.mark.parametrize("invalid", (True, 1.0))
def test_two_wire_digit_law_rejects_numeric_aliases(invalid: object) -> None:
    with pytest.raises(TypeError):
        collatz_digit_carry_wires(invalid)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        collatz_digit_carry_wires(1, base=invalid)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        mul3_carry_monoid(invalid)  # type: ignore[arg-type]


def test_two_wire_law_declines_radices_without_independent_thresholds() -> None:
    for base in (2, 3, 5, 6, 8):
        with pytest.raises(ValueError, match="1 modulo 3"):
            collatz_digit_carry_wires(0, base=base)


def test_two_wire_constructor_rejects_nonstaircase_actions() -> None:
    with pytest.raises(ValueError, match="staircase"):
        CollatzCarryWires(CarryFn.CONST0, CarryFn.ID)
