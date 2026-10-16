"""Expensive exhaustive checks for the double-reversal border graph."""

from __future__ import annotations

import random
from dataclasses import dataclass
from itertools import product

import pytest

from number_compiler.sequences.double_reverse.boundary_cycles import (
    CANDIDATE_COMPONENTS,
    Edge,
    boundary_steps,
    candidate_component,
    edge_from_digits,
)
from number_compiler.sequences.double_reverse.temporal_carry_safety import (
    component_safety_proof,
)


@dataclass(frozen=True, slots=True)
class _GlobalBorderSafetyProof:
    original_edges: int
    collapsed_dag_nodes: int
    candidate_scc_count: int
    maximum_steps_to_standard_or_shrink: int
    component_bounds: tuple[int, int, int, int]


def _global_border_distances() -> tuple[_GlobalBorderSafetyProof, dict[Edge, int]]:
    """Validation-only exhaustive research oracle over the complete edge graph."""
    vertices: tuple[Edge, ...] = tuple(
        (a, b, y, z) for a, b, y, z in product(range(10), repeat=4) if a > 0
    )
    if len(vertices) != 9000:
        raise AssertionError("complete decimal edge enumeration was truncated")
    identified: dict[Edge, int] = {
        edge: component
        for component, edges in enumerate(CANDIDATE_COMPONENTS)
        for edge in edges
    }

    def key(edge: Edge) -> int | Edge:
        return identified.get(edge, edge)

    adjacent: dict[int | Edge, set[int | Edge]] = {}
    for edge in vertices:
        source = key(edge)
        outgoing = adjacent.setdefault(source, set())
        for transition in boundary_steps(edge).steps:
            target = key(transition.target)
            if target != source:
                outgoing.add(target)
    if len(adjacent) != 9000 - sum(map(len, CANDIDATE_COMPONENTS)) + 4:
        raise AssertionError("SCC condensation lost a border state")
    indegree = {node: 0 for node in adjacent}
    for targets in adjacent.values():
        for node in targets:
            indegree[node] += 1
    queue = [node for node, degree in indegree.items() if degree == 0]
    order: list[int | Edge] = []
    while queue:
        node = queue.pop()
        order.append(node)
        for successor in adjacent[node]:
            indegree[successor] -= 1
            if indegree[successor] == 0:
                queue.append(successor)
    if len(order) != len(adjacent):
        raise AssertionError("two-cell border graph has an unclassified SCC")

    bounds = {0: 0}
    for component in (1, 2, 3):
        maximum = component_safety_proof(component).maximum_internal_transitions
        if maximum is None:
            raise AssertionError("conditional border SCC has no finite exit proof")
        bounds[component] = maximum
    remaining: dict[int | Edge, int] = {0: 0}
    for node in reversed(order):
        if node == 0:
            continue
        cost = bounds.get(node, 0) if isinstance(node, int) else 0
        remaining[node] = (
            cost
            + 1
            + max((remaining[successor] for successor in adjacent[node]), default=0)
        )
    return (
        _GlobalBorderSafetyProof(
            len(vertices),
            len(adjacent),
            len(CANDIDATE_COMPONENTS),
            max(remaining.values()),
            (0, remaining[1], remaining[2], remaining[3]),
        ),
        {edge: remaining[key(edge)] for edge in vertices},
    )


def _literal(x: int) -> int:
    return 2 * int(str(x)[::-1])


@pytest.mark.validation
def test_all_9000_edge_states_reach_standard_or_shrink_within_30() -> None:
    # Component lifting eliminated every indefinite alternative SCC. The
    # remaining 8979-node SCC-condensed graph is acyclic; its weighted
    # longest-path computation is a complete, source-independent proof.
    # Compute this global graph once: the resulting edge-distance map is the
    # oracle for all 9,000 entry points, instead of rebuilding the graph for
    # every call to the public single-edge query.
    proof, distances = _global_border_distances()
    assert (
        proof.original_edges,
        proof.collapsed_dag_nodes,
        proof.candidate_scc_count,
        proof.maximum_steps_to_standard_or_shrink,
        proof.component_bounds,
    ) == (9000, 8979, 4, 30, (0, 7, 7, 13))
    assert len(distances) == 9000
    assert (
        max(
            distances[(a, b, y, z)]
            for a in range(1, 10)
            for b in range(10)
            for y in range(10)
            for z in range(10)
        )
        == 30
    )
    for i, component in enumerate(CANDIDATE_COMPONENTS):
        assert all(distances[edge] == proof.component_bounds[i] for edge in component)


@pytest.mark.validation
def test_independent_trajectories_respect_entry_or_shrink_bound() -> None:
    rng = random.Random(20261015)
    seeds = list(range(10_000, 20_000))
    seeds += [
        rng.randrange(10 ** (w - 1), 10**w) for w in range(5, 16) for _ in range(100)
    ]
    observed = 0
    for seed in seeds:
        source = seed
        for _step in range(31):
            previous = str(source)
            if candidate_component(edge_from_digits(previous)) == 0:
                observed += 1
                break
            successor = _literal(source)
            if len(str(successor)) < len(previous):
                observed += 1
                break
            source = successor
        else:
            raise AssertionError(f"missing 30-step entry-or-shrink boundary: {seed}")
    assert observed == len(seeds)
