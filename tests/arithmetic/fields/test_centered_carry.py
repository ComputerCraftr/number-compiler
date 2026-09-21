"""Bounded polynomial oracles for the centered residual's symbolic arithmetic.

Explicit polynomials below are test oracles, never a production extractor.
"""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.centered_carry import (
    advance_centered_residual,
    carry_coboundary,
    center_pair_field,
    reflected_innovation,
    uncenter_pair_field,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    SymbolicInnovationArena,
    _Add,
    _Charted,
    _Interval,
    _Radial,
    _Scale,
    _Zero,
)
from number_compiler.resources.ledger import ResourceLedger


def _polynomial(arena: SymbolicInnovationArena, word: list[int]) -> InnovationID:
    one = arena.interval(1)
    return arena.linear_combination(
        tuple(
            (coefficient, arena.chart(one, CylinderChart(1, -index)))
            for index, coefficient in enumerate(word)
            if coefficient
        )
    )


def _evaluate(arena: SymbolicInnovationArena, root: InnovationID) -> dict[int, int]:
    """Independent bounded full Laurent-polynomial oracle, without quotient loss."""
    memo: dict[InnovationID, dict[int, int]] = {}
    stack = [(root, False)]
    while stack:
        ref, ready = stack.pop()
        if ref in memo:
            continue
        node = arena.resolve(ref)
        if not ready:
            stack.append((ref, True))
            if isinstance(node, _Add):
                stack.extend(((node.left, False), (node.right, False)))
            elif isinstance(node, (_Charted, _Scale, _Radial)):
                stack.append((node.child, False))
            continue
        result: dict[int, int]
        if isinstance(node, _Zero):
            result = {}
        elif isinstance(node, _Interval):
            assert node.length <= 32
            result = dict.fromkeys(range(node.length), 1)
        elif isinstance(node, _Add):
            result = memo[node.left].copy()
            for index, value in memo[node.right].items():
                result[index] = result.get(index, 0) + value
        elif isinstance(node, _Scale):
            result = {i: node.coefficient * v for i, v in memo[node.child].items()}
        elif isinstance(node, _Charted):
            assert node.chart.extent_scale == node.chart.growth_scale == 0
            result = {
                node.chart.slope * (i - node.chart.offset): v
                for i, v in memo[node.child].items()
            }
        elif isinstance(node, _Radial):
            assert node.multiplier.growth <= 20
            assert node.multiplier.no_growth <= 20
            result = {
                i: (1 << node.multiplier.no_growth) * v
                for i, v in memo[node.child].items()
            }
            for _ in range(node.multiplier.growth):
                before = result.copy()
                for index, value in before.items():
                    result[index + 1] = result.get(index + 1, 0) + value
        else:
            raise TypeError("test oracle received an unevaluated source atom")
        memo[ref] = {i: v for i, v in result.items() if v}
    return memo[root]


@pytest.mark.parametrize("seed", [0, 1, 5, 6, 9, 18, 196, 292, 909, 1041, 1051, 1593])
def test_centered_self_advance_matches_twenty_literal_steps(seed: int) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    digits = [int(d) for d in str(seed)[::-1]]
    pair = [a + b for a, b in zip(digits, reversed(digits), strict=True)]
    residual = center_pair_field(arena, _polynomial(arena, pair), extent=len(pair))
    for _ in range(20):
        width = len(digits)
        carry = 0
        output: list[int] = []
        outgoing: list[int] = []
        for i in range(width):
            total = digits[i] + digits[-1 - i] + carry
            carry, digit = divmod(total, 10)
            output.append(digit)
            outgoing.append(carry)
        if carry:
            output.append(carry)
        # Only the bounded reference supplies Q here. This does not exercise
        # or claim an implemented source-to-clock constructor.
        correction = carry_coboundary(arena, _polynomial(arena, outgoing), base=10)
        beta = reflected_innovation(arena, correction, extent=width, growth=carry)
        residual = advance_centered_residual(
            arena, residual, beta, extent=width, growth=carry
        )
        pairs = [a + b for a, b in zip(output, reversed(output), strict=True)]
        assert _evaluate(arena, residual) == {
            i: value - 9 for i, value in enumerate(pairs) if value != 9
        }
        assert _evaluate(
            arena, uncenter_pair_field(arena, residual, extent=len(output))
        ) == {i: v for i, v in enumerate(pairs) if v}
        digits = output
    if seed == 196:
        assert digits == [int(d) for d in "70446464506"[::-1]]


def test_all_neutral_residual_is_not_a_temporal_identity() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    after = advance_centered_residual(arena, arena.zero, arena.zero, extent=4, growth=0)
    assert _evaluate(arena, after) == dict.fromkeys(range(4), 9)


def test_one_cell_growth_has_no_interior_window_correction() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    one = arena.interval(1)
    residual = arena.linear_combination(((9, one),))
    correction = carry_coboundary(arena, one, base=10)
    beta = reflected_innovation(arena, correction, extent=1, growth=1)
    result = advance_centered_residual(arena, residual, beta, extent=1, growth=1)
    assert _evaluate(arena, result) == {}


def test_same_reset_sign_and_tail_do_not_merge_different_residual_magnitudes() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    one = arena.interval(1)
    correction = carry_coboundary(arena, one, base=10)
    beta = reflected_innovation(arena, correction, extent=1, growth=1)
    # Source digits 5 and 6: centered pair coefficients are 1 and 3. Both
    # have h=0, positive reset, and empty tail, but their successors differ.
    first = advance_centered_residual(arena, one, beta, extent=1, growth=1)
    second = advance_centered_residual(
        arena, arena.linear_combination(((3, one),)), beta, extent=1, growth=1
    )
    assert first != second
    assert _evaluate(arena, first) == {0: -8, 1: -8}
    assert _evaluate(arena, second) == {0: -6, 1: -6}


@pytest.mark.parametrize("growth", [0, 1])
def test_centered_arithmetic_does_not_expand_huge_extent(growth: int) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    width = 10**200
    delta = center_pair_field(arena, arena.zero, extent=width)
    before = arena.node_count
    advance_centered_residual(arena, delta, arena.zero, extent=width, growth=growth)
    assert arena.node_count - before <= 6
    assert ledger.counters["centered_carry_algebra_advance_attempts"] == 1
    assert "symbolic_innovation_projection_visits" not in ledger.counters


def test_foreign_or_stale_operand_is_rejected_before_allocating() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    foreign = SymbolicInnovationArena(ResourceLedger())
    before = arena.node_count
    with pytest.raises(ValueError):
        advance_centered_residual(
            arena, arena.zero, foreign.zero, extent=10**200, growth=1
        )
    assert arena.node_count == before
    stale = arena.zero
    arena.close()
    with pytest.raises(ValueError):
        center_pair_field(arena, stale, extent=5)


@pytest.mark.parametrize(("extent", "growth"), [(0, 0), (1, 2), (True, 0), (1, False)])
def test_invalid_geometry_is_rejected(extent: int, growth: int) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    with pytest.raises((TypeError, ValueError)):
        advance_centered_residual(
            arena, arena.zero, arena.zero, extent=extent, growth=growth
        )
    assert arena.node_count == 1
