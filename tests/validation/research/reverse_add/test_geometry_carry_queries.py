"""Exact geometry supplies pointwise carries omitted by a harmonic projection."""

import gc
from itertools import product

import pytest

from devtools.verification.carry_harmonic_ports import CarryHarmonicPortAction
from devtools.verification.reverse_threshold_geometry import ThresholdGeometry
from devtools.verification.threshold_expressions import ThresholdExpressions
from number_compiler.arithmetic.automata import program_word as words
from number_compiler.arithmetic.carry.carry_monoid import CarryFn, apply_carry_fn
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded


def test_prefix_queries_and_simultaneous_substitution_use_only_geometry() -> None:
    e = ThresholdExpressions()
    g = ThresholdGeometry(e)
    domains = tuple(e.variable(3, i) for i in range(4))
    incoming = e.variable(2, 4)
    root = g.from_domains(domains)
    queries = tuple(g.carry_at(root, i, incoming) for i in range(5))
    swapped = e.substitute(queries, {**dict(enumerate(domains[::-1])), 4: incoming})
    for values in product(range(3), repeat=4):
        for port in (0, 1):
            expected = [port]
            reflected = [port]
            for domain in values:
                expected.append(apply_carry_fn(tuple(CarryFn)[domain], expected[-1]))
            for domain in values[::-1]:
                reflected.append(apply_carry_fn(tuple(CarryFn)[domain], reflected[-1]))
            assert e.evaluate(queries, (*values, port)) == tuple(expected)
            assert e.evaluate(swapped, (*values, port)) == tuple(reflected)
    assert {n.data[0] for n in e.nodes if n.kind == "variable"} == set(range(5))
    for bad in (-1, 6, True):
        with pytest.raises(ValueError):
            g.carry_at(root, bad, incoming)
    with pytest.raises(ValueError, match="foreign"):
        ThresholdGeometry(e).carry_at(root, 1, incoming)


def test_geometry_fills_the_harmonic_gap_without_a_new_residual() -> None:
    rows = ((2, 0, 0, 0), (0, 0, 2, 0))
    actions = [
        CarryHarmonicPortAction.from_domains(tuple(tuple(CarryFn)[d] for d in row))
        for row in rows
    ]
    assert actions[0].rows == actions[1].rows
    e = ThresholdExpressions()
    g = ThresholdGeometry(e)
    carry_one: list[int] = []
    for row in rows:
        root = g.from_domains(tuple(e.constant(3, d) for d in row))
        carry_one.append(e.evaluate((g.carry_at(root, 1, e.constant(2, 0)),), ())[0])
    assert carry_one == [1, 0]
    assert not any(n.kind == "variable" for n in e.nodes)


def test_counted_geometry_queries_do_not_expand_uniform_regions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    e = ThresholdExpressions()
    g = ThresholdGeometry(e)
    value = e.constant(10, 5)
    huge = g.uniform(value, value, 10**100)  # GT throughout.
    incoming = e.variable(2, 0)

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("carry query expanded the geometry")

    monkeypatch.setattr(g, "coordinates", forbidden)
    monkeypatch.setattr(words, "iter_runs", forbidden)
    for i in (1, 10**50, 10**100):
        assert g.carry_at(huge, i, incoming) == e.constant(2, 1)
    assert g.carry_at(huge, 0, incoming) == incoming
    assert g.summary_cache_entries == 1
    assert len(e.nodes) < 10


def test_carry_monoid_eliminates_dead_prefix_dependencies() -> None:
    e = ThresholdExpressions()
    old = e.variable(3, 0)
    incoming = e.variable(2, 1)
    identity, reset = e.constant(3, 1), e.constant(3, 2)
    assert e.carry_compose(identity, old) == old
    assert e.carry_compose(old, identity) == old
    assert e.carry_compose(old, old) == old
    assert e.carry_compose(reset, old) == reset
    carry = e.carry_apply(e.carry_compose(reset, old), incoming)
    assert e.evaluate((carry,), ()) == (1,)
    with pytest.raises(ValueError, match="sorts"):
        e.carry_apply(incoming, old)


def test_geometry_summary_lifetime_and_budget_are_explicit() -> None:
    e = ThresholdExpressions(max_nodes=5)
    g = ThresholdGeometry(e)
    domain = e.variable(3, 0)
    root = g.from_domains((domain,))
    g.prefix_action(root, 1)
    assert e.auxiliary_nodes == 1
    # A live summary consumes the same budget as expression/schema nodes.
    e.constant(2, 0)
    e.constant(2, 1)
    with pytest.raises(BlockContextBudgetExceeded):
        e.constant(5, 0)
    del root
    gc.collect()
    assert e.auxiliary_nodes == 0 and g.summary_cache_entries == 0
    root = g.from_domains((domain,))
    g.prefix_action(root, 1)
    assert e.auxiliary_nodes == 1
    del g
    gc.collect()
    assert e.auxiliary_nodes == 0
