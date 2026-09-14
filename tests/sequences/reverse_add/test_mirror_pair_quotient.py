"""Exact tests for the correlated no-growth mirror-pair consumer."""

from __future__ import annotations

from itertools import product
from typing import cast

import pytest

from devtools.proofs.reverse_geometry_context import ReverseGeometryContext
from devtools.proofs.threshold_expressions import (
    MIRROR_DOMAIN_CLASSES,
    MIRROR_DOMAIN_ROWS,
    MIRROR_PAIR_TABLE,
    ThresholdExpressions,
)
from number_compiler.arithmetic.carry.carry_monoid import CarryFn, value_carry_fn
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_cocycle_coordinates,
    decimal_normalize_cocycle,
    decimal_normalized_pair_sum,
)


def test_mirror_pair_and_domain_chart_are_exact_for_all_ports() -> None:
    expressions = ThresholdExpressions()
    for residue, left, right in product(range(10), range(2), range(2)):
        carry_sum = left + right
        full = expressions.mirror_pair(
            expressions.constant(10, residue),
            expressions.constant(3, carry_sum),
        )
        domain = expressions.mirror_pair(
            expressions.constant(10, residue),
            expressions.constant(3, carry_sum),
            domain_only=True,
        )
        expected = decimal_normalized_pair_sum(residue, left, residue, right)
        assert MIRROR_PAIR_TABLE[3 * residue + carry_sum] == expected
        assert expressions.evaluate((full, domain), ()) == (
            expected,
            tuple(CarryFn).index(value_carry_fn(expected, 10)),
        )
    assert MIRROR_DOMAIN_ROWS == ((0, 0, 0), (0, 1, 2), (2, 2, 2), (2, 1, 0))
    assert MIRROR_DOMAIN_CLASSES == (0, 0, 0, 0, 1, 2, 2, 2, 2, 3)


def test_source_plus_ten_has_27_fixed_port_aliases() -> None:
    expressions = ThresholdExpressions()
    aliases = 0
    for source, carry_sum in product(range(9), range(3)):
        left, right = carry_sum == 2, carry_sum > 0
        expected = decimal_normalized_pair_sum(source, int(left), source, int(right))
        shifted = decimal_normalized_pair_sum(
            source + 10, int(left), source + 10, int(right)
        )
        assert expected == shifted
        residue = expressions.constant(10, source)
        shifted_residue = expressions.constant(10, (source + 10) % 10)
        carry = expressions.constant(3, carry_sum)
        assert expressions.mirror_pair(residue, carry) == expressions.mirror_pair(
            shifted_residue, carry
        )
        aliases += 1
    assert aliases == 27


def test_domain_only_merges_same_response_row_but_full_outputs_do_not() -> None:
    expressions = ThresholdExpressions()
    residue = expressions.variable(2, 0)
    carry = expressions.variable(3, 1)
    left = expressions.table(residue, 10, (0, 4))
    right = expressions.table(residue, 10, (3, 4))
    left_domain = expressions.mirror_pair(left, carry, domain_only=True)
    right_domain = expressions.mirror_pair(right, carry, domain_only=True)
    assert left_domain == right_domain
    assert expressions.mirror_pair(left, carry) != expressions.mirror_pair(right, carry)
    for source, port in product(range(2), range(3)):
        expected_row = MIRROR_DOMAIN_CLASSES[(0, 4)[source]]
        expected = MIRROR_DOMAIN_ROWS[expected_row][port]
        assert expressions.evaluate((left_domain,), (source, port))[0] == expected


def test_simultaneous_substitution_handles_full_and_domain_native_nodes() -> None:
    expressions = ThresholdExpressions()
    residue = expressions.variable(10, 0)
    carry = expressions.variable(3, 1)
    full = expressions.mirror_pair(residue, carry)
    domain = expressions.mirror_pair(residue, carry, domain_only=True)
    replaced = expressions.substitute(
        (full, domain),
        {0: expressions.constant(10, 8), 1: expressions.constant(3, 2)},
    )
    assert expressions.evaluate(replaced, ()) == (18, 2)


def test_mirror_outputs_epsilon_depends_only_on_carry_ports() -> None:
    context = ReverseGeometryContext(2)
    e = context.expressions
    alpha = e.variable(5, 0)
    old_parity = e.variable(2, 1)
    left_carry = e.variable(2, 2)
    right_carry = e.variable(2, 3)
    _domain, _alpha, epsilon = context._mirror_outputs(
        alpha, old_parity, left_carry, right_carry
    )
    reachable = e.reachable((epsilon,))
    assert alpha.index not in reachable
    assert old_parity.index not in reachable
    assert {left_carry.index, right_carry.index} <= reachable


@pytest.mark.parametrize(
    ("source", "expected"),
    (
        ((10, 10, 10, 10), (1, 2, 2, 2, 1)),
        ((10, 15, 15, 10), (1, 7, 12, 7, 1)),
    ),
)
def test_growth_keeps_value_alignment_and_old_parity(
    source: tuple[int, ...], expected: tuple[int, ...]
) -> None:
    output, growth = pair_step(source, 10)
    assert growth == 1 and output == expected
    context = ReverseGeometryContext(5)
    action = context.primitive()
    assert context.observe(action, context.binding(source)) == expected
    assert context.metrics(action)["growth_full19_value_fallbacks"] == 0
    assert context.metrics(action)["growth_generic_parity_tables"] == 0

    current = tuple(decimal_cocycle_coordinates(value) for value in source)
    next_coordinates = tuple(decimal_cocycle_coordinates(value) for value in output)
    assert tuple(row[0] for row in current) == (CarryFn.CONST1,) * 4
    assert tuple(row[1] for row in current) == (0,) * 4
    if source == (10, 10, 10, 10):
        assert tuple(row[2] for row in current) == (0,) * 4
    else:
        assert tuple(row[2] for row in current) == (0, 1, 1, 0)
    assert tuple(row[2] for row in next_coordinates) == (
        (1, 0, 0, 0, 1) if source == (10, 10, 10, 10) else (1, 1, 0, 1, 1)
    )


def test_crt_normalization_matches_residue_plus_carry_for_20_cases() -> None:
    expressions = ThresholdExpressions()
    residue_variable, carry_variable = (
        expressions.variable(10, 0),
        expressions.variable(2, 1),
    )
    normalized = expressions.affine(10, ((residue_variable, 1), (carry_variable, 1)))
    for residue, carry in product(range(10), range(2)):
        _domain, alpha, epsilon = decimal_cocycle_coordinates(residue)
        expected_coordinates = decimal_normalize_cocycle(alpha, epsilon, carry)
        # Reconstruct the same CRT digit through the expression coordinates.
        alpha_expr = expressions.constant(5, alpha)
        epsilon_expr = expressions.constant(2, epsilon)
        parity = expressions.table(alpha_expr, 2, (0, 1, 0, 1, 0))
        beta = expressions.affine(2, ((parity, 1), (epsilon_expr, 1)))
        high = expressions.table(beta, 6, (0, 5))
        reconstructed = expressions.affine(10, ((alpha_expr, 1), (high, 1)))
        assert expressions.evaluate((reconstructed,), ()) == (residue,)
        assert expressions.evaluate((normalized,), (residue, carry)) == (
            (residue + carry) % 10,
        )
        assert (
            expected_coordinates
            == decimal_cocycle_coordinates((residue + carry) % 10)[1:]
        )


def test_decimal_sum_domain_is_commutative_and_exact_for_100_inputs() -> None:
    expressions = ThresholdExpressions()
    left = expressions.variable(10, 0)
    right = expressions.variable(10, 1)
    direct = expressions.decimal_sum_domain(left, right)
    swapped = expressions.decimal_sum_domain(right, left)
    assert direct == swapped
    assert expressions.substitute((direct,), {0: right, 1: left}) == (direct,)
    for first, second in product(range(10), repeat=2):
        expected = tuple(CarryFn).index(value_carry_fn(first + second, 10))
        assert expressions.evaluate((direct,), (first, second)) == (expected,)


def test_native_mirror_and_decimal_sum_reject_bad_sorts_and_budgets() -> None:
    expressions = ThresholdExpressions()
    with pytest.raises(ValueError):
        expressions.mirror_pair(expressions.constant(9, 0), expressions.constant(3, 0))
    with pytest.raises(ValueError):
        expressions.mirror_pair(
            expressions.constant(10, 0),
            expressions.constant(3, 0),
            domain_only=cast(bool, 1),
        )
    with pytest.raises(ValueError):
        expressions.decimal_sum_domain(
            expressions.constant(10, 0), expressions.constant(3, 0)
        )

    tiny = ThresholdExpressions(max_nodes=3)
    residue = tiny.variable(10, 0)
    carry = tiny.variable(3, 1)
    with pytest.raises(BlockContextBudgetExceeded):
        tiny.mirror_pair(residue, carry, domain_only=True)
