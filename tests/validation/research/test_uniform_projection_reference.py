"""Bounded differential evidence for the research-only uniform output projections."""

from __future__ import annotations

import pytest

from devtools.experiments.reverse_add.uniform_projection_reference import (
    UniformPumpUnavailable,
    edge_core_successors,
    select_clause,
    uniform_no_growth_power,
    uniform_source_admitted,
    uniform_successor,
)


def _literal_pair_successor(source: tuple[int, ...]) -> tuple[tuple[int, ...], int]:
    """Normalize literal digits, then reflect; no grammar branch equations."""
    carry, digits = 0, []
    for pair in source:
        carry, digit = divmod(pair + carry, 10)
        digits.append(digit)
    if carry:
        digits.append(carry)
    target = tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))
    return target, carry


def test_uniform_primitive_clauses_match_literal_pair_equations() -> None:
    for symbol in range(19):
        clause = uniform_successor(symbol)
        for width in range(1, 13):
            expected, growth = _literal_pair_successor((symbol,) * width)
            assert clause.instantiate(width) == expected
            assert clause.growth == growth


def test_first_edge_core_family_matches_literal_pair_equations() -> None:
    for edge in range(1, 9):
        clauses = edge_core_successors(edge, 2 * edge)
        for parameter in range(1, 13):
            source = (edge,) + (2 * edge,) * (parameter - 1) + (edge,)
            expected, growth = _literal_pair_successor(source)
            clause = select_clause(clauses, parameter)
            assert clause.instantiate(parameter) == expected
            assert clause.growth == growth == 0


@pytest.mark.parametrize(
    ("symbol", "events", "target"),
    ((0, 10**9, 0), (1, 4, 16), (2, 3, 16), (4, 2, 16), (9, 1, 18)),
)
def test_repeated_no_growth_uniform_rule_is_constant_size(
    symbol: int, events: int, target: int
) -> None:
    clause = uniform_no_growth_power(symbol, events)
    assert clause.events == events
    assert clause.runs[0].symbol == target
    assert clause.admits(10**30)
    if events < 20:
        literal: tuple[int, ...] = (symbol,) * 7
        for _ in range(events):
            literal, growth = _literal_pair_successor(literal)
            assert growth == 0
        assert clause.instantiate(7) == literal


@pytest.mark.parametrize(("symbol", "events"), ((1, 5), (4, 3), (5, 2), (9, 2)))
def test_repeated_no_growth_rule_refuses_first_growth_exit(
    symbol: int, events: int
) -> None:
    with pytest.raises(UniformPumpUnavailable, match="exits"):
        uniform_no_growth_power(symbol, events)


def test_source_occurrence_guard_keeps_parity_and_zero_conventions_explicit() -> None:
    assert uniform_source_admitted(0, 1)
    assert not uniform_source_admitted(0, 2)
    assert uniform_source_admitted(7, 2)
    assert not uniform_source_admitted(7, 1)
    assert not uniform_source_admitted(7, 3)
    assert uniform_source_admitted(8, 1)
    assert uniform_source_admitted(8, 3)
    assert not uniform_source_admitted(19, 2)


def test_general_edge_core_and_boundary_core_are_unowned_successors() -> None:
    clauses = edge_core_successors(5, 10)
    generalized = select_clause(clauses, 2)
    boundary = select_clause(clauses, 4)
    assert generalized.target_shape == "edge-core"
    assert generalized.instantiate(2) == (11, 0, 11)
    assert boundary.target_shape == "boundary-core"
    assert boundary.instantiate(4) == (11, 1, 2, 1, 11)
    with pytest.raises(UniformPumpUnavailable, match="outside"):
        edge_core_successors(9, 18)
    with pytest.raises(UniformPumpUnavailable, match="outside"):
        edge_core_successors(5, 11)
