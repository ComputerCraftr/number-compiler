"""Chronological compressed carry words retain order and exact prefixes."""

from __future__ import annotations

from collections.abc import Sequence

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.carry.signed_weighted_carry import (
    WideSignedCarryAction,
)


def _reference_emit(
    coefficients: Sequence[int], initial: int
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    carry = initial
    boundaries = [carry]
    digits: list[int] = []
    for coefficient in coefficients:
        total = coefficient + carry
        digit = total & 1
        carry = (total - digit) // 2
        digits.append(digit)
        boundaries.append(carry)
    return tuple(digits), tuple(boundaries)


def test_repeated_compressed_block_preserves_interleaved_order_and_prefixes() -> None:
    arena = SLPArena()
    first = arena.word((1, 2))
    second = arena.word((4, 1))
    block = arena.concat(first, second)
    repeated = arena.repeat(block, 5)
    incorrect_grouped = arena.concat(arena.repeat(first, 5), arena.repeat(second, 5))

    assert arena.nodes[repeated].length == 20
    assert arena.nodes[incorrect_grouped].length == 20

    action = WideSignedCarryAction(arena, repeated, sign=1)
    grouped_action = WideSignedCarryAction(arena, incorrect_grouped, sign=1)
    chronological_coefficients = (1, 2, 4, 1) * 5
    grouped_coefficients = (1, 2) * 5 + (4, 1) * 5
    expected_digits, expected_boundaries = _reference_emit(
        chronological_coefficients, action.c0
    )
    grouped_digits, _ = _reference_emit(grouped_coefficients, grouped_action.c0)

    assert expected_digits != grouped_digits
    assert tuple(action.digit_at(i) for i in range(20)) == expected_digits
    assert tuple(action.carry_at(i) for i in range(21)) == expected_boundaries
    assert action.verify_cochain()
    assert action.block.value != grouped_action.block.value


def test_compressed_word_prefix_handles_full_blocks_and_incomplete_remainder() -> None:
    arena = SLPArena()
    block = arena.word((3, 0, 2))
    root = arena.concat(arena.repeat(block, 4), arena.word((1, 0)))
    action = WideSignedCarryAction(arena, root, sign=1)
    coefficients = (3, 0, 2) * 4 + (1, 0)
    expected_digits, expected_boundaries = _reference_emit(coefficients, action.c0)

    # Each boundary samples a prefix that may end in the repeated block or in
    # its finite tail. The production summary keeps the REPEAT node compressed.
    assert tuple(action.carry_at(i) for i in range(len(coefficients) + 1)) == (
        expected_boundaries
    )
    assert tuple(action.digit_at(i) for i in range(len(coefficients))) == (
        expected_digits
    )
