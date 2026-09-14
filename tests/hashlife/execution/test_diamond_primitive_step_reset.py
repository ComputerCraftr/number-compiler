"""Complete one-letter right resets simplify before expression interning."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherEmit,
    HigherStep,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
from number_compiler.hashlife.observation.diamond_parametric_query import (
    parametric_point,
)
from tests.support.diamond_halos import suffix_parity
from tests.support.diamond_observation_adversarial import neighbor_xor
from tests.support.diamond_primitive_step_reset import machine
from tests.support.diamond_query import build, oracle


def test_certified_step_matches_every_primitive_incoming_state_and_symbol() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    kernel = runtime.kernel(action)
    assert runtime.resets.radius(action) == 1
    for symbol in range(kernel.blank + 1):
        results = set()
        for value in range(kernel.right_count):
            state = arena.literal(runtime.boundaries.literal(action, 1, value))
            result = runtime.execute(
                HigherStep(action, 1, state, arena.symbol(action, symbol))
            )
            results.add(result)
            assert runtime.execute(LowerFinite(result)) == kernel.advance(
                BoundarySide.RIGHT, value, symbol
            )
        assert len(results) == 1
    assert runtime.ledger.counters["higher_primitive_right_reset_elisions"] > 0


def test_nested_complete_continuations_alias_after_erasing_earlier_expressions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    x = arena.variable(arena.state_sort(action, 1), "outer-state")
    y = arena.variable(arena.state_sort(action, 1), "inner-state")
    left = arena.literal(runtime.boundaries.literal(action, 0, 0))
    final_symbol = runtime.execute(HigherEmit(action, left, arena.symbol(action, 1), x))
    first = arena.primitive_advance(action, 1, y, arena.symbol(action, 0))
    second = arena.primitive_advance(action, 1, y, arena.symbol(action, 1))
    assert first != second
    initial = arena.literal(
        runtime.boundaries.literal(
            action, 1, runtime.kernel(action).initial(BoundarySide.RIGHT)
        )
    )
    advance = arena.primitive_advance

    def observe(
        effect: ActionProgramID, side: int, incoming: ExprID, symbol: ExprID
    ) -> ExprID:
        if effect == action and side == 1:
            assert incoming == initial, (
                "erased earlier program reached expression interning"
            )
        return advance(effect, side, incoming, symbol)

    monkeypatch.setattr(arena, "primitive_advance", observe)
    a = runtime.execute(HigherStep(action, 1, first, final_symbol))
    b = runtime.execute(HigherStep(action, 1, second, final_symbol))
    assert a == b
    inner_a, inner_b = arena.lambda_(y, a), arena.lambda_(y, b)
    assert inner_a == inner_b
    assert arena.constant_function(inner_a) == a
    whole = runtime.actions.compose(action, action)
    complete_a = arena.lambda_(
        x,
        arena.pair(
            whole,
            1,
            a,
            arena.lambda_(arena.variable(arena.state_sort(action, 0), "opposite"), a),
        ),
    )
    complete_b = arena.lambda_(
        x,
        arena.pair(
            whole,
            1,
            b,
            arena.lambda_(arena.variable(arena.state_sort(action, 0), "opposite"), b),
        ),
    )
    assert complete_a == complete_b


@pytest.mark.parametrize("warm", (False, True))
def test_foreign_or_malformed_state_is_rejected_before_reset_shortcuts(
    warm: bool,
) -> None:
    runtime, action = machine()
    other, foreign_action = machine()
    arena = runtime.higher.expressions
    state = arena.literal(runtime.boundaries.literal(action, 1, 0))
    symbol = arena.symbol(action, 1)
    foreign = other.higher.expressions.literal(
        other.boundaries.literal(foreign_action, 1, 0)
    )
    if warm:
        runtime.execute(HigherStep(action, 1, state, symbol))
    invalids = (
        foreign,
        ExprID(arena.token, "wrong-kind", state.local_id),
        ExprID(arena.token, "diamond-boundary-expression", len(arena.nodes)),
    )
    for invalid in invalids:
        task = HigherStep(action, 1, invalid, symbol)
        for operation in (runtime.execute, runtime.higher.probe):
            before = runtime.ledger.snapshot()
            with pytest.raises(ValueError):
                operation(task)
            assert runtime.ledger.snapshot() == before


def test_uncertified_right_transition_preserves_its_input() -> None:
    runtime, action = machine(suffix_parity())
    arena = runtime.higher.expressions
    incoming = arena.variable(arena.state_sort(action, 1), "parity-input")
    symbol = arena.symbol(action, 1)
    assert runtime.resets.radius(action) is None
    result = runtime.execute(HigherStep(action, 1, incoming, symbol))
    assert arena.node(result).children[0] == incoming.local_id
    assert not runtime.ledger.counters.get("higher_primitive_right_reset_elisions", 0)


@pytest.mark.parametrize("steps", (1, 2, 3, 4))
def test_small_exact_orbits_preserve_every_output(steps: int) -> None:
    kernel = neighbor_xor()
    source = (0, 1, 1, 0)
    app = build(kernel, source, 8, steps)
    expected = oracle(kernel, source, 8, steps)
    assert [
        parametric_point(app.runtime, app.root, position) for position in range(8)
    ] == expected


def test_distinct_erased_programs_share_one_observation_key_before_execution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    variable = arena.variable(arena.state_sort(action, 1), "earlier-program")
    first = arena.primitive_advance(action, 1, variable, arena.symbol(action, 0))
    second = arena.primitive_advance(action, 1, variable, arena.symbol(action, 1))
    symbol = arena.symbol(action, 2)
    assert first != second
    expected = runtime.execute(HigherStep(action, 1, first, symbol))
    keys = [key for key in runtime.higher.observations if type(key) is HigherStep]
    assert len(keys) == 1
    canonical = arena.literal(
        runtime.boundaries.literal(
            action, 1, runtime.kernel(action).initial(BoundarySide.RIGHT)
        )
    )
    assert keys[0] == HigherStep(action, 1, canonical, symbol)
    before = runtime.ledger.snapshot()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm reset action replayed its primitive generator")

    monkeypatch.setattr(runtime.higher, "_step", forbidden)
    assert runtime.execute(HigherStep(action, 1, second, symbol)) == expected
    assert (
        len([key for key in runtime.higher.observations if type(key) is HigherStep])
        == 1
    )
    assert runtime.ledger.entries == before.entries
    assert runtime.ledger.nodes == before.nodes
    assert (
        runtime.ledger.counters["higher_context_cache_hits"]
        == before.counters.get("higher_context_cache_hits", 0) + 1
    )


@pytest.mark.parametrize("warm", (False, True))
@pytest.mark.parametrize("kind", ("step", "initial", "unary", "context"))
def test_wrong_sort_or_foreign_published_result_rejects_before_reset_allocation(
    warm: bool, kind: str
) -> None:
    runtime, action = machine()
    other, foreign_action = machine()
    arena = runtime.higher.expressions
    incoming = arena.variable(arena.state_sort(action, 1), "publication-input")
    request: HigherStep | HigherInitial | HigherUnaryObserve | HigherObserve = (
        HigherStep(action, 1, incoming, arena.symbol(action, 1))
    )
    if kind != "step":
        from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
            HigherInitial,
            HigherObserve,
            HigherSummary,
            HigherUnaryObserve,
            HigherUnarySummary,
        )

        initial = runtime.execute(HigherInitial(action, 1))
        if kind == "initial":
            request = HigherInitial(action, 1)
        elif kind == "unary":
            parent = runtime.execute(
                HigherUnarySummary(action, runtime.cells.source(0, 1), 1)
            )
            request = HigherUnaryObserve(parent, initial)
        else:
            parent = runtime.execute(
                HigherSummary(action, action, runtime.cells.source(0, 1))
            )
            left = runtime.execute(HigherInitial(action, 0))
            request = HigherObserve(parent, left, initial, initial, 1)
    if warm:
        runtime.execute(request)
    wrong_sort = arena.symbol(action, 1)
    foreign = other.higher.expressions.literal(
        other.boundaries.literal(foreign_action, 1, 0)
    )
    for result in (wrong_sort, foreign):
        before = runtime.ledger.snapshot()
        with pytest.raises(ValueError):
            runtime.higher.publish(request, result)
        assert runtime.ledger.snapshot() == before


def test_singleton_right_port_erases_symbol_program_before_warm_lookup(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    runtime, action = machine(DigitNormalizeBlockEffect(2))
    arena = runtime.higher.expressions
    assert runtime.resets.radius(action) == 0
    left = arena.variable(arena.state_sort(action, 0), "provider-left")
    right = arena.literal(runtime.boundaries.literal(action, 1, 0))
    first = arena.primitive_emit(action, left, arena.symbol(action, 0), right)
    second = arena.primitive_emit(action, left, arena.symbol(action, 1), right)
    assert first != second
    initial = runtime.execute(HigherStep(action, 1, right, first))
    keys = [key for key in runtime.higher.observations if type(key) is HigherStep]
    assert keys == [HigherStep(action, 1, right, arena.symbol(action, 0))]
    assert arena.node(keys[0].symbol).kind == "symbol"
    assert initial == right
    before = runtime.ledger.snapshot()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "singleton exit must not evaluate any symbol or primitive step"
        )

    monkeypatch.setattr(runtime.higher, "_step", forbidden)
    assert runtime.execute(HigherStep(action, 1, right, second)) == right
    assert runtime.ledger.entries == before.entries
    assert runtime.ledger.nodes == before.nodes
    assert (
        runtime.ledger.counters["higher_context_cache_hits"]
        == before.counters.get("higher_context_cache_hits", 0) + 1
    )
    wrong_sort = left
    foreign, foreign_action = machine(DigitNormalizeBlockEffect(2))
    foreign_symbol = foreign.higher.expressions.symbol(foreign_action, 1)
    for invalid in (wrong_sort, foreign_symbol):
        before = runtime.ledger.snapshot()
        with pytest.raises(ValueError):
            runtime.execute(HigherStep(action, 1, right, invalid))
        assert runtime.ledger.snapshot() == before
