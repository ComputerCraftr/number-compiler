"""Chronological compressed carry words retain order and exact prefixes."""

from __future__ import annotations

from collections.abc import Sequence
from typing import NoReturn

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.arithmetic.carry import signed_weighted_carry
from number_compiler.arithmetic.carry.signed_weighted_carry import (
    MAX_SIGNED_WEIGHTED_BITS,
    WeightedCarryBlock,
    WideSignedCarryAction,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.private_attributes import set_private_test_attribute


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


def test_signed_carry_demand_rejects_same_id_source_node_replacement() -> None:
    arena = SLPArena()
    left = arena.terminal(2)
    right = arena.terminal(0)
    root = arena.concat(left, right)
    action = WideSignedCarryAction(arena, root, sign=1)
    generation = arena.node_id_generation

    arena.nodes[left] = SLPNode(left, "TERM", 1, symbol=0)

    assert arena.node_id_generation > generation
    with pytest.raises(RuntimeError, match="node IDs changed"):
        action.demand((1,))
    with pytest.raises(RuntimeError, match="stale interners"):
        WideSignedCarryAction(arena, root, sign=1)


def test_signed_carry_demand_pins_exact_node_storage() -> None:
    arena = SLPArena()
    root = arena.word((2, 0))
    action = WideSignedCarryAction(arena, root, sign=1)

    object.__setattr__(arena, "nodes", list(arena.nodes))

    with pytest.raises(RuntimeError, match="source arena or root changed"):
        action.demand((1,))
    with pytest.raises(RuntimeError, match="stale interners"):
        WideSignedCarryAction(arena, root, sign=1)


@pytest.mark.parametrize(
    ("coefficients", "sign", "signed_minus_one"),
    (
        ((1, 2, 4, 1) * 3 + (1, 0), 1, False),
        ((1, 2, 4, 1) * 3 + (1, 0), -1, False),
        ((0, 0, 0, 2), -1, True),
    ),
)
def test_verify_cochain_checks_weighted_seam_without_expanding_coefficients(
    coefficients: tuple[int, ...],
    sign: int,
    signed_minus_one: bool,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = SLPArena()
    if signed_minus_one:
        root = arena.word(coefficients)
    else:
        repeated_block = arena.word(coefficients[:4])
        finite_tail = arena.word(coefficients[12:])
        root = arena.concat(arena.repeat(repeated_block, 3), finite_tail)

    action = WideSignedCarryAction(arena, root, sign=sign)
    assert action.signed_minus_one is signed_minus_one
    if signed_minus_one:
        assert tuple(action.digit_at(i) for i in range(action.width)) == (-1, 0, 0, 0)
        assert tuple(action.carry_at(i) for i in range(action.width + 1)) == (
            -1,
            0,
            0,
            0,
            1,
        )
    else:
        expected_digits, expected_boundaries = _reference_emit(coefficients, action.c0)
        assert tuple(action.digit_at(i) for i in range(action.width)) == expected_digits
        assert tuple(action.carry_at(i) for i in range(action.width + 1)) == (
            expected_boundaries
        )

    original_carry_at = action.carry_at
    boundary_visits: list[int] = []
    positions = (action.width - 1, 0, 2)
    expected_demand = tuple(
        (position, action.digit_at(position), original_carry_at(position))
        for position in positions
    )

    def count_carry_at(boundary: int) -> int:
        boundary_visits.append(boundary)
        return original_carry_at(boundary)

    def reject_digit_at(_position: int) -> NoReturn:
        raise AssertionError("cochain verification redundantly called digit_at")

    monkeypatch.setattr(action, "carry_at", count_carry_at)
    monkeypatch.setattr(action, "digit_at", reject_digit_at)
    assert action.demand(positions) == expected_demand
    assert boundary_visits == list(positions)
    boundary_visits.clear()

    def reject_prefix_query(_boundary: int) -> NoReturn:
        raise AssertionError("cochain verification rebuilt a source prefix")

    monkeypatch.setattr(action, "carry_at", reject_prefix_query)

    def reject_word_expansion(_arena: SLPArena, _root: int, _position: int) -> NoReturn:
        raise AssertionError("cochain verification expanded the coefficient word")

    monkeypatch.setattr(signed_weighted_carry, "symbol_at", reject_word_expansion)
    assert action.verify_cochain()
    assert boundary_visits == []


@pytest.mark.parametrize("sign", (-1, 1))
@pytest.mark.parametrize("coefficients", ((-4, 3, -1, 2), (-1, -2, -3), (7, -3, 5)))
def test_signed_weighted_seam_matches_literal_negative_coefficients(
    sign: int, coefficients: tuple[int, ...]
) -> None:
    arena = SLPArena()
    action = WideSignedCarryAction(arena, arena.word(coefficients), sign=sign)
    carry = action.c0
    for position, coefficient in enumerate(coefficients):
        digit = (
            -1
            if action.signed_minus_one and position == 0
            else (coefficient + carry) % 2
        )
        assert action.digit_at(position) == digit
        assert (coefficient + carry - digit) % 2 == 0
        carry = (coefficient + carry - digit) // 2
        assert action.carry_at(position + 1) == carry
    assert carry == sign * action.c0
    assert action.verify_cochain()


@pytest.mark.parametrize("field", ("block", "c0", "sign"))
def test_verify_cochain_rejects_tampered_summary_and_seam_fields(field: str) -> None:
    arena = SLPArena()
    root = arena.word((1, 2, 4, 1, 0))
    action = WideSignedCarryAction(arena, root, sign=1)
    if field == "block":
        action.block = WeightedCarryBlock(action.block.length, action.block.value + 1)
    elif field == "c0":
        action.c0 += 1
    else:
        action.sign = -1
    assert not action.verify_cochain()


@pytest.mark.parametrize("tamper", ("interior", "missing", "extra", "bool_key"))
def test_verify_cochain_revalidates_each_retained_summary_row(tamper: str) -> None:
    arena = SLPArena()
    left = arena.terminal(1)
    right = arena.terminal(2)
    root = arena.concat(left, right)
    action = WideSignedCarryAction(arena, root, sign=1)
    rows = {
        left: WeightedCarryBlock(1, 1),
        right: WeightedCarryBlock(1, 2),
        root: WeightedCarryBlock(2, 5),
    }
    set_private_test_attribute(action, "_summaries", rows)
    assert action.verify_cochain()

    if tamper == "interior":
        rows[left] = WeightedCarryBlock(1, 0)
    elif tamper == "missing":
        del rows[left]
    elif tamper == "extra":
        rows[99] = WeightedCarryBlock(0, 0)
    else:
        value = rows.pop(left)
        rows[True] = value
    assert not action.verify_cochain()


@pytest.mark.parametrize("field", ("length", "value"))
@pytest.mark.parametrize("independent_block", (False, True))
def test_verify_cochain_rejects_boolean_aliases_in_frozen_blocks(
    field: str, independent_block: bool
) -> None:
    arena = SLPArena()
    action = WideSignedCarryAction(arena, arena.word((1,)), sign=1)
    if independent_block:
        action.block = WeightedCarryBlock(action.block.length, action.block.value)
    object.__setattr__(action.block, field, True)
    assert not action.verify_cochain()


def test_verify_recomputes_one_summary_per_repeat_node_not_every_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    count = 4096
    arena = SLPArena()
    root = arena.repeat(arena.word((1, 2)), count)
    action = WideSignedCarryAction(arena, root, sign=1)
    original_then = WeightedCarryBlock.then
    compositions = 0

    def counted_then(
        self: WeightedCarryBlock,
        other: WeightedCarryBlock,
        *,
        max_length: int,
        max_weighted_bits: int = MAX_SIGNED_WEIGHTED_BITS,
    ) -> WeightedCarryBlock:
        nonlocal compositions
        compositions += 1
        return original_then(
            self,
            other,
            max_length=max_length,
            max_weighted_bits=max_weighted_bits,
        )

    monkeypatch.setattr(WeightedCarryBlock, "then", counted_then)

    def reject_prefix_query(_boundary: int) -> NoReturn:
        raise AssertionError("verification queried a repeated growing prefix")

    monkeypatch.setattr(action, "carry_at", reject_prefix_query)
    assert action.verify_cochain()
    assert compositions <= 2 * count.bit_length() + 2


def test_signed_carry_rejects_reused_arena_node_ids() -> None:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "signed-carry-generation", "test")
    try:
        root = arena.word((1, 2))
        action = WideSignedCarryAction(arena, root, sign=1)
        original_generation = arena.node_id_generation

        arena.rollback_unpublished_suffix(1)
        assert arena.node_id_generation > original_generation
        reused_root = arena.concat(arena.terminal(3), arena.terminal(4))
        assert reused_root == root

        with pytest.raises(RuntimeError, match="source node IDs changed"):
            action.carry_at(1)
        with pytest.raises(RuntimeError, match="source node IDs changed"):
            action.digit_at(0)
        with pytest.raises(RuntimeError, match="source node IDs changed"):
            action.verify_cochain()

        arena.dispose()
        with pytest.raises(ValueError, match="disposed ledgered SLP arena"):
            action.carry_at(1)
    finally:
        arena.dispose()
    assert ledger.entries == 0
    assert ledger.nodes == 0
