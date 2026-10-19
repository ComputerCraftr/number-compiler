"""Finite boundary-relation audit and exact T² normalization regressions."""

from __future__ import annotations

from itertools import product

import pytest

from number_compiler.sequences.double_reverse.boundary_cycles import (
    CANDIDATE_COMPONENTS,
    BoundaryStep,
    boundary_steps,
    candidate_component,
    edge_from_digits,
    width_change,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm


def _audit_graph() -> dict[tuple[int, int, int, int], tuple[BoundaryStep, ...]]:
    return {
        (a, b, y, z): boundary_steps((a, b, y, z)).steps
        for a, b, y, z in product(range(10), repeat=4)
        if a > 0
    }


def _audit_cyclic_components(
    graph: dict[tuple[int, int, int, int], tuple[BoundaryStep, ...]],
) -> tuple[frozenset[tuple[int, int, int, int]], ...]:
    follow = {
        source: tuple(step.target for step in steps) for source, steps in graph.items()
    }
    reverse: dict[tuple[int, int, int, int], list[tuple[int, int, int, int]]] = {
        source: [] for source in graph
    }
    for source, targets in follow.items():
        for target in targets:
            reverse[target].append(source)
    visited: set[tuple[int, int, int, int]] = set()
    order: list[tuple[int, int, int, int]] = []
    for source in graph:
        if source in visited:
            continue
        visited.add(source)
        stack = [(source, 0)]
        while stack:
            vertex, index = stack[-1]
            if index == len(follow[vertex]):
                stack.pop()
                order.append(vertex)
                continue
            child = follow[vertex][index]
            stack[-1] = (vertex, index + 1)
            if child not in visited:
                visited.add(child)
                stack.append((child, 0))
    assigned: set[tuple[int, int, int, int]] = set()
    groups: list[frozenset[tuple[int, int, int, int]]] = []
    for source in reversed(order):
        if source in assigned:
            continue
        assigned.add(source)
        group = {source}
        reverse_stack = [source]
        while reverse_stack:
            vertex = reverse_stack.pop()
            for previous in reverse[vertex]:
                if previous not in assigned:
                    assigned.add(previous)
                    group.add(previous)
                    reverse_stack.append(previous)
        if len(group) > 1 or source in follow[source]:
            groups.append(frozenset(group))
    return tuple(sorted(groups, key=lambda group: (-len(group), sorted(group))))


def test_exact_9000_state_boundary_graph_has_four_cyclic_components() -> None:
    graph = _audit_graph()
    assert len(graph) == 9000
    assert sum(not steps for steps in graph.values()) == 450
    assert sum(len(steps) for steps in graph.values()) == 12600
    assert set(_audit_cyclic_components(graph)) == set(CANDIDATE_COMPONENTS)
    for index, component in enumerate(CANDIDATE_COMPONENTS):
        for edge in component:
            assert candidate_component(edge) == index
    exits = []
    for component in CANDIDATE_COMPONENTS:
        exits.append(
            sum(
                step.target not in component
                for vertex in component
                for step in boundary_steps(vertex).steps
            )
        )
    assert exits == [0, 1, 2, 2]


@pytest.mark.parametrize(
    "exhaustive", [False, pytest.param(True, marks=pytest.mark.validation)]
)
def test_every_five_digit_source_agrees_with_relation_and_width_law(
    exhaustive: bool,
) -> None:
    # Threshold edges on both sides of each carry gate and both inward carries.
    sources = (
        range(10_000, 100_000)
        if exhaustive
        else (
            10000 * a + 1000 * b + 100 * c + 10 * y + z
            for a, b, c, y, z in product(
                (1, 4, 5, 9), (0, 4, 5, 9), (0, 9), (0, 4, 5, 9), (0, 1, 4, 5, 9)
            )
        )
    )
    outcomes = set()
    for number in sources:
        source = str(number)
        successor = 2 * int(source[::-1])
        assert len(str(successor)) - 5 == width_change(source)
        relation = boundary_steps(edge_from_digits(source))
        outcomes.add((relation.shrinking_frontier, len(str(successor)) - 5 > 0))
        if relation.shrinking_frontier:
            assert not relation.steps
            assert len(str(successor)) < len(source)
        else:
            assert (edge_from_digits(str(successor)), len(str(successor)) - 5) in {
                (step.target, step.width_delta) for step in relation.steps
            }

    assert outcomes == {(True, False), (False, False), (False, True)}


def test_normalized_square_handles_shrinking_source_examples() -> None:
    for seed in (0, 5, 10, 50, 100, 502, 5330, 410, 176330, 4910):
        first = 2 * int(str(seed)[::-1])
        expected = 2 * int(str(first)[::-1])
        with DoubleReverseTerm(seed, 2, max_state_bits=512) as term:
            assert term.materialize(max_bits=512) == expected
            assert (
                term.metrics().get("double_reverse_temporal_square_applications", 0)
                == 1
            )
            assert (
                term.metrics().get("double_reverse_spatial_transducer_applications", 0)
                == 0
            )


def test_candidate_sccs_are_explicit_diagnostics_never_temporal_authority() -> None:
    for seed, component in ((16488, 1), (1697542, 2), (16922, 3)):
        with DoubleReverseTerm(seed, 2, max_state_bits=512) as term:
            candidate = term._adapter.temporal_hashlife.candidate_cycle(
                term._source.root
            )
            assert candidate == component
            expected = 2 * int(str(2 * int(str(seed)[::-1]))[::-1])
            assert term.materialize(max_bits=512) == expected
            metrics = term.metrics()
            assert metrics.get("double_reverse_temporal_hashlife_publications", 0) == 0


def test_shrinking_candidate_uses_the_guarded_exact_square() -> None:
    with DoubleReverseTerm(176330, 2, max_state_bits=512) as term:
        assert term.materialize(max_bits=512) == 48752
        metrics = term.metrics()
        assert metrics.get("double_reverse_temporal_square_normalizations", 0) >= 1
        assert metrics.get("double_reverse_temporal_square_shrink_seams", 0) >= 1


def test_trailing_zero_count_powers_slp_repeats_without_expansion() -> None:
    with DoubleReverseTerm(2, 2, max_state_bits=256) as term:
        arena = term._arena
        source = arena.concat(
            arena.word((1, 2, 3)), arena.repeat(arena.terminal(0), 10**12)
        )
        assert term._adapter._trailing_zero_count(source) == 10**12
        assert term._adapter.temporal_hashlife.part(source, 0, 3) == arena.word(
            (1, 2, 3)
        )
