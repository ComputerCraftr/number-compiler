"""Balanced carry arithmetic retains exact source, prefixes and audit authority."""

from __future__ import annotations

from typing import NoReturn

import pytest

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.carry.signed_weighted_carry import (
    SignedCarryBudgetExceeded,
    WideSignedCarryAction,
)
from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_integer_tuple,
    is_object_tuple,
)
from tests.support.private_attributes import (
    private_test_attribute,
    set_private_test_attribute,
)


def _left_deep(arena: SLPArena, coefficients: tuple[int, ...]) -> int:
    root = arena.empty()
    for coefficient in coefficients:
        root = arena.concat(root, arena.terminal(coefficient))
    return root


@pytest.mark.parametrize("sign", (-1, 1))
def test_balanced_plan_has_small_retained_weight_and_exact_prefixes(
    sign: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    coefficients = (2, 0, -3, 5) * 1024
    arena = SLPArena()
    root = _left_deep(arena, coefficients)
    action = WideSignedCarryAction(arena, root, sign=sign)
    assert action.retained_weighted_bits < 16 * len(coefficients)
    assert action.block.value == sum(value << i for i, value in enumerate(coefficients))

    def forbidden(*_args: object, **_kwargs: object) -> NoReturn:
        raise AssertionError(
            "compact prefixes must not descend the original skew grammar"
        )

    monkeypatch.setattr(
        "number_compiler.arithmetic.carry.signed_weighted_carry.symbol_at", forbidden
    )
    boundaries = {0, 1, 63, 64, 65, 1024, 4095, 4096}
    carry = action.c0
    for i, coefficient in enumerate(coefficients):
        if i in boundaries:
            assert action.carry_at(i) == carry
            assert action.digit_at(i) == (coefficient + carry) % 2
        carry = (coefficient + carry) // 2
    assert action.carry_at(len(coefficients)) == carry == sign * action.c0
    assert action.verify_cochain()
    assert action.verify_cochain()


def test_balanced_plan_repeat_keeps_chronology_and_incomplete_tail() -> None:
    arena = SLPArena()
    coefficients = (1, -2, 4) * 384
    block = _left_deep(arena, coefficients)
    root = arena.concat(arena.repeat(block, 31), arena.word((7, -1)))
    action = WideSignedCarryAction(arena, root, sign=1)
    for position in (
        0,
        len(coefficients) - 1,
        len(coefficients),
        30 * len(coefficients) + 17,
        action.width - 1,
    ):
        expected = (
            coefficients[position % len(coefficients)]
            if position < 31 * len(coefficients)
            else -1
        )
        assert (
            action.demand((position,))[0][1]
            == (expected + action.carry_at(position)) % 2
        )
    assert action.retained_weighted_bits < 4 * action.width
    assert action.verify_cochain()


def test_balanced_audit_rejects_equal_weight_but_different_prefix_data() -> None:
    arena = SLPArena()
    action = WideSignedCarryAction(
        arena, _left_deep(arena, (2, 0, 3, -1) * 1024), sign=1
    )
    plan = private_test_attribute(action, "_plan")
    rows = private_test_attribute(plan, "rows")
    assert is_object_tuple(rows)
    first = rows[0]
    symbols = private_test_attribute(first, "symbols")
    assert is_exact_integer_tuple(symbols)
    assert symbols[:2] == (2, 0)
    original = action.carry_at(1)
    # 2 + 2*0 = 0 + 2*1: the full weighted action is unchanged, but the
    # intermediate carry is not. A root-only audit would miss the forgery.
    object.__setattr__(first, "symbols", (0, 1, *symbols[2:]))
    assert action.carry_at(1) == original - 1
    assert not action.verify_cochain()


@pytest.mark.parametrize("tamper", ("missing", "root_alias", "extra_row"))
def test_balanced_audit_rejects_changed_plan_shape(tamper: str) -> None:
    arena = SLPArena()
    action = WideSignedCarryAction(arena, _left_deep(arena, (1, 0) * 1024), sign=1)
    plan = private_test_attribute(action, "_plan")
    if tamper == "missing":
        set_private_test_attribute(action, "_plan", None)
    elif tamper == "root_alias":
        object.__setattr__(plan, "root", True)
    else:
        rows = private_test_attribute(plan, "rows")
        assert is_object_tuple(rows)
        object.__setattr__(plan, "rows", (*rows, rows[0]))
    assert not action.verify_cochain()


def test_balanced_plan_respects_integer_budget_before_large_coefficients() -> None:
    arena = SLPArena()
    root = _left_deep(arena, (1, 0) * 1024)
    with pytest.raises(SignedCarryBudgetExceeded):
        WideSignedCarryAction(arena, root, sign=1, max_weighted_bits=64)
