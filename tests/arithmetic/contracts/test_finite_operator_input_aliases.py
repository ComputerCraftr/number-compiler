"""Exact public operator and budget admission before state/table lookup."""

from __future__ import annotations

from array import array
from collections.abc import Callable
from typing import TYPE_CHECKING, TypedDict, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect


class FiniteKernelArguments(TypedDict):
    base: int
    exponent: int
    left_count: int
    right_count: int
    alphabet_size: int
    initial_left: int
    initial_right: int
    left_transitions: array[int]
    right_transitions: array[int]
    outputs: bytes
    kernel_name: str
    storage_bytes: int
    uncompressed_bytes: int
    blank_left_tail: int
    blank_right_tail: int
    stable_blank_output: bool


class BudgetArguments(TypedDict, total=False):
    max_nodes: int | None
    max_cache_entries: int | None
    created_nodes: int
    cache_entries: int


def finite(
    **changes: object,
) -> FiniteBlockEffect:
    arguments: dict[str, object] = dict(
        base=2,
        exponent=1,
        left_count=1,
        right_count=1,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 4),
        right_transitions=array("I", [0] * 4),
        outputs=bytes(range(4)),
        kernel_name="identity",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
    arguments.update(changes)
    return FiniteBlockEffect(**cast("FiniteKernelArguments", arguments))


@pytest.mark.parametrize("value", (True, 1.0, "1"))
@pytest.mark.parametrize(
    "field",
    (
        "base",
        "exponent",
        "left_count",
        "right_count",
        "alphabet_size",
        "initial_left",
        "initial_right",
        "storage_bytes",
        "uncompressed_bytes",
        "blank_left_tail",
        "blank_right_tail",
    ),
)
def test_finite_constructor_rejects_numeric_aliases_before_payload_copy(
    field: str, value: bool | float | str
) -> None:
    with pytest.raises(TypeError):
        finite(**{field: value, "left_transitions": object()})


@pytest.mark.parametrize("value", (True, 0.0, "0", -1, 4))
@pytest.mark.parametrize(
    "method",
    ("advance-state", "advance-symbol", "emit-left", "emit-right", "emit-symbol"),
)
def test_finite_observations_reject_invalid_payload_before_table_lookup(
    value: bool | float | int | str, method: str
) -> None:
    effect = finite()
    effect.advance(BoundarySide.LEFT, 0, 0)
    effect.emit(0, 0, 0)
    with pytest.raises((TypeError, ValueError)):
        if method == "advance-state":
            effect.advance(BoundarySide.LEFT, value, 0)
        elif method == "advance-symbol":
            effect.advance(BoundarySide.LEFT, 0, cast("int", value))
        elif method == "emit-left":
            effect.emit(value, 0, 0)
        elif method == "emit-right":
            effect.emit(0, 0, value)
        else:
            effect.emit(0, cast("int", value), 0)


@pytest.mark.parametrize("factory", (finite, lambda: BaseBlockEffect(2)))
@pytest.mark.parametrize("side", (True, 0, 0.0, "0"))
def test_kernel_sides_have_an_exact_enum_sort(
    factory: Callable[[], FiniteBlockEffect | BaseBlockEffect],
    side: bool | float | int | str,
) -> None:
    effect = factory()
    with pytest.raises(TypeError):
        effect.initial(cast("BoundarySide", side))
    with pytest.raises(TypeError):
        effect.boundary_universe(cast("BoundarySide", side))
    with pytest.raises(TypeError):
        effect.advance(cast("BoundarySide", side), effect.initial(BoundarySide.LEFT), 0)


@pytest.mark.parametrize(
    "field", ("max_nodes", "max_cache_entries", "created_nodes", "cache_entries")
)
@pytest.mark.parametrize("value", (True, 2.0, "2", -1))
def test_budget_construction_and_mutation_reject_invalid_values(
    field: str, value: bool | float | int | str
) -> None:
    with pytest.raises((TypeError, ValueError)):
        BlockContextBudget(**cast("BudgetArguments", {field: value}))
    budget = BlockContextBudget(5, 5)
    before = vars(budget).copy()
    with pytest.raises((TypeError, ValueError)):
        setattr(budget, field, value)
    assert vars(budget) == before


@pytest.mark.parametrize(
    "method", ("consume_node", "consume_cache", "check_spacetime_nodes")
)
@pytest.mark.parametrize("value", (True, 2.0, "2", -1))
def test_budget_consumption_rejects_aliases_without_mutation(
    method: str, value: bool | float | int | str
) -> None:
    budget = BlockContextBudget(5, 5)
    before = vars(budget).copy()
    with pytest.raises((TypeError, ValueError)):
        getattr(budget, method)(value)
    assert vars(budget) == before


@pytest.mark.parametrize("base", (2, 3, 5, 10, 12, 31))
@pytest.mark.parametrize("side", tuple(BoundarySide))
def test_closed_primitive_domain_preserves_independent_breadth_first_order(
    base: int, side: BoundarySide
) -> None:
    from collections import deque

    effect = BaseBlockEffect(base)
    initial = effect.initial(side)
    found = {initial}
    states = [initial]
    pending = deque(states)
    while pending:
        state = pending.popleft()
        for symbol in range(effect.blank + 1):
            target = effect.advance(side, state, symbol)
            if target not in found:
                found.add(target)
                states.append(target)
                pending.append(target)
    assert effect.boundary_universe(side) == tuple(states)
    assert effect.boundary_universe(side, max_states=len(states) - 1) is None
    assert effect.boundary_universe(side, max_states=len(states)) == tuple(states)
