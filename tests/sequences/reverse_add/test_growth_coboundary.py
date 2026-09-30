"""Carry gauges disappear at the growth consumer, before output publication."""

from itertools import product

import pytest

from devtools.verification.growth_coboundary import (
    GROWTH_SYMBOLS,
    GrowthCoboundaryHalf,
    growth_symbol_value,
)
from devtools.verification.reverse_geometry_context import ReverseGeometryContext
from devtools.verification.threshold_expressions import ThresholdExpressions
from number_compiler.arithmetic.carry.event_memory import carry_field, pair_step


def test_four_distinct_sources_have_one_growth_occurrence() -> None:
    occurrences = set()
    for a, b in product((1, 10), repeat=2):
        source = (10, a, b, b, a, 10)
        carry = carry_field(source)
        symbols = tuple(
            growth_symbol_value(source[i] % 10, carry[i + 1], carry[6 - i])
            for i in range(3)
        )
        occurrence = GrowthCoboundaryHalf(6, symbols)
        occurrences.add(occurrence)
        assert occurrence.output_half() == (1, 2, 2, 2)
        assert pair_step(source, 10) == ((1, 2, 2, 2, 2, 2, 1), 1)
        context = ReverseGeometryContext(7, growth_quotient=True)
        action = context.primitive()
        assert context.observe(action, context.binding(source)) == (1, 2, 2, 2, 2, 2, 1)
    assert occurrences == {GrowthCoboundaryHalf(6, (1, 1, 1))}


def test_native_chart_consumes_only_residue_and_derived_ports() -> None:
    e = ThresholdExpressions()
    r, c, d = e.variable(10, 0), e.variable(2, 1), e.variable(2, 2)
    chart = e.growth_symbol(r, c, d)
    seen = set()
    for residue, outgoing, reflected in product(range(10), range(2), range(2)):
        symbol = e.evaluate((chart,), (residue, outgoing, reflected))[0]
        seen.add(symbol)
        q, delta = GROWTH_SYMBOLS[symbol]
        assert q == (residue + outgoing) % 10
        if residue == 9 or outgoing == reflected:
            assert delta == reflected - outgoing
    assert seen == set(range(12))
    first = e.substitute(
        (chart,), {0: e.constant(10, 1), 1: e.constant(2, 0), 2: e.constant(2, 0)}
    )
    second = e.substitute(
        (chart,), {0: e.constant(10, 0), 1: e.constant(2, 1), 2: e.constant(2, 1)}
    )
    assert first == second == (e.constant(12, 1),)


def test_native_growth_emits_planes_without_exact_pair_node() -> None:
    e = ThresholdExpressions()
    left, right = e.variable(12, 0), e.variable(12, 1)
    outputs = e.growth_channels(left, right)
    assert all(e.nodes[i].size != 19 for i in e.reachable(outputs))
    for a, b in product(range(10), repeat=2):
        value = a + b
        assert e.evaluate(outputs, (a, b)) == (
            (value > 9) + (value >= 9),
            value % 5,
            value % 2,
        )
    pulled = e.substitute(outputs, {0: right, 1: left})
    assert e.evaluate(pulled, (10, 1)) == e.evaluate(outputs, (1, 10))


def test_joint_value_carry_gauge_merges_before_publication() -> None:
    e = ThresholdExpressions()
    choice = e.variable(2, 0)
    residue = e.table(choice, 10, (1, 0))
    outgoing = e.table(choice, 2, (0, 1))
    # The source chooses LT coefficient 1 or GT coefficient 10. Their residue
    # and carry functions differ, yet the resulting symbol is identically q=1.
    symbol = e.growth_symbol(residue, outgoing, outgoing)
    assert symbol == e.constant(12, 1)
    assert e.resolve(symbol).args == ()
    assert e.growth_gauge_alias_hits == 1


def test_growth_occurrence_rejects_malformed_symbols() -> None:
    with pytest.raises(ValueError):
        GrowthCoboundaryHalf(4, (12, 1))
    with pytest.raises(ValueError):
        GrowthCoboundaryHalf(4, (1, 11)).output_half()
    e = ThresholdExpressions()
    with pytest.raises(ValueError):
        e.growth_symbol(e.constant(19, 0), e.constant(2, 0), e.constant(2, 0))
