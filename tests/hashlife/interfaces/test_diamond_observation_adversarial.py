"""A finite state sort alone does not make a cached observation an action."""

from __future__ import annotations

from random import Random

import pytest

from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
    ResolveExpr,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherUnarySummary,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    ExprID,
    StateSort,
    SymbolSort,
)
from number_compiler.hashlife.observation.diamond_parametric_query import (
    parametric_point,
)
from tests.support.diamond_observation_adversarial import (
    bound_observation_fixture,
    bound_projection_fixture,
    neighbor_xor,
    structured_projection,
)
from tests.support.diamond_query import build, oracle
from tests.support.diamond_quotient import (
    capture_root_emissions,
)


def test_public_points_cannot_cache_intermediate_symbols_disguised_as_finite_states(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    kernel = neighbor_xor()
    rng = Random(765)
    source = tuple(rng.randrange(2) for _ in range(24))
    app = build(kernel, source, 32, 2)
    runtime = app.runtime
    arena = runtime.higher.expressions
    outputs = capture_root_emissions(app, monkeypatch)
    expected = oracle(kernel, source, 32, 2)
    for position in range(24):
        assert parametric_point(runtime, app.root, position) == expected[position]
    intermediate = oracle(kernel, source, 32, 1)
    recovered = []
    observations = getattr(runtime, "boundary_observations", {})
    for position, output in enumerate(outputs):
        node = arena.node(output)
        assert node.kind == "emit"
        right = arena._handle(node.children[2])
        assert type(arena.node(right).sort) is StateSort
        cached = observations.get(LowerFinite(right))
        if cached is not None:
            recovered.append((right, arena.node(cached).value))
            assert arena.node(cached).value == intermediate[position + 1]
    # This guard detects the previous 24 distinct ExprID -> literal entries,
    # whose values exactly encoded positions1..24 of the unrequested T field.
    assert not recovered, (
        "syntax-bound finite observations retain a lossless future symbol tape"
    )
    for task in runtime.expression_heads:
        assert type(task) is ResolveExpr
        assert arena.node(task.expression).free_ports, (
            "closed observation escaped through the head memo"
        )
        assert type(arena.node(task.expression).sort) is not SymbolSort


@pytest.mark.parametrize("warm", (False, True))
def test_foreign_finite_observation_rejected_before_any_cache_shortcut(
    warm: bool,
) -> None:
    app = build(neighbor_xor(), (0, 1, 1), 8, 2)
    other = build(neighbor_xor(), (0, 1, 1), 8, 2)
    runtime, arena = app.runtime, app.runtime.higher.expressions
    action = runtime.actions.reference(runtime.actions.node(app.root).first)
    literal = arena.literal(runtime.boundaries.literal(action, 1, 0))
    foreign_action = other.runtime.actions.reference(
        other.runtime.actions.node(other.root).first
    )
    foreign = other.runtime.higher.expressions.literal(
        other.runtime.boundaries.literal(foreign_action, 1, 0)
    )
    if warm:
        assert runtime.execute(LowerFinite(literal)) == 0
    before = runtime.ledger.snapshot()
    for expression in (
        foreign,
        ExprID(arena.token, "diamond-boundary-expression", len(arena.nodes)),
    ):
        for task in (LowerFinite(expression), ResolveExpr(expression)):
            with pytest.raises(ValueError):
                runtime.execute(task)
            with pytest.raises(ValueError):
                runtime._probe(task)
    assert runtime.ledger.snapshot() == before


def test_warm_canonical_parent_skips_source_and_compiler_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    app = build(neighbor_xor(), (0, 1, 1, 0, 1, 0, 0, 1), 8, 2)
    runtime = app.runtime
    cell = runtime.cells.source(0, 3)
    request = HigherUnarySummary(app.root, cell, 1)
    first = runtime.execute(request)

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("warm parent replayed its source or spatial children")

    monkeypatch.setattr(runtime.cells, "source_symbol", forbidden)
    monkeypatch.setattr(runtime.cells, "split", forbidden)
    monkeypatch.setattr(runtime.higher, "program", forbidden)
    assert runtime.execute(request) == first


@pytest.mark.parametrize("structured", (False, True))
def test_bound_projection_results_do_not_acquire_substitution_response_bindings(
    structured: bool,
) -> None:
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
        ExprBinding,
        ExprSubstitutionKey,
    )

    ledger, arena, variable, incoming, expression, expected, right = (
        bound_projection_fixture()
    )
    if structured:
        expression, expected = structured_projection(
            arena, variable, right, expression, expected
        )
    key = ExprSubstitutionKey(expression, (ExprBinding(variable, incoming),))
    before = ledger.snapshot()
    ledger.max_cache_entries = ledger.entries
    assert arena.substitute(expression, {variable: incoming}) == expected
    assert key not in arena.memo
    assert ledger.entries == before.entries
    assert ledger.nodes == before.nodes
    assert ledger.counters["boundary_expression_bound_result_memo_drops"] > 0


def test_higher_observation_drops_a_realized_result_with_bound_program_input() -> None:
    from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
        HigherUnaryObserve,
    )

    _app, runtime, arena, action, bound = bound_observation_fixture()
    assert arena.node(bound).kind == "call"
    parent = runtime.execute(HigherUnarySummary(action, runtime.cells.source(0, 1), 1))
    task = HigherUnaryObserve(parent, bound)
    result = runtime.execute(task)
    assert arena.node(result).kind == "literal"
    assert task not in runtime.higher.observations
    assert runtime.ledger.counters["higher_context_bound_result_memo_drops"] > 0


@pytest.mark.parametrize("steps", (2, 4))
def test_all_retained_response_stores_obey_bound_realized_result_boundary(
    steps: int,
) -> None:
    from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
        HigherInitial,
        HigherObserve,
        HigherStep,
        HigherUnaryObserve,
    )

    rng = Random(765)
    source = tuple(rng.randrange(2) for _ in range(24))
    app = build(neighbor_xor(), source, 32, steps)
    runtime, arena = app.runtime, app.runtime.higher.expressions
    expected = oracle(neighbor_xor(), source, 32, steps)
    for position in range(24):
        assert parametric_point(runtime, app.root, position) == expected[position]

    def realized(expression: ExprID) -> bool:
        pending, seen = [expression.local_id], set()
        while pending:
            index = pending.pop()
            if index in seen:
                continue
            seen.add(index)
            node = arena.nodes[index]
            if node.kind not in ("literal", "symbol", "pair", "lambda", "bound"):
                return False
            pending.extend(node.children)
        return True

    def bound(expression: ExprID) -> bool:
        node = arena.node(expression)
        if node.free_ports or node.kind in ("literal", "symbol"):
            return False
        return not (
            node.kind == "finite_apply"
            and arena.nodes[node.children[0]].kind == "literal"
        )

    for key, value in arena.memo.items():
        assert not (
            realized(value) and any(bound(binding.value) for binding in key.bindings)
        )
    inputs: tuple[ExprID, ...]
    for higher_key, value in runtime.higher.observations.items():
        if type(higher_key) is HigherInitial:
            continue
        if type(higher_key) is HigherStep:
            inputs = higher_key.state, higher_key.symbol
        elif type(higher_key) is HigherObserve:
            inputs = higher_key.left, higher_key.right, higher_key.incoming
        else:
            assert type(higher_key) is HigherUnaryObserve
            inputs = (higher_key.state,)
        assert not (realized(value) and any(bound(argument) for argument in inputs))
