"""Focused tests for deferred simultaneous higher-port binding."""

from __future__ import annotations

from collections.abc import Callable
from typing import Never, cast

import pytest

from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
)
from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
from tests.hashlife.execution.test_higher_semantic import SchemaFixture, arena_fixture
from tests.hashlife.execution.test_higher_temporal_image import (
    temporal_construction_fixture,
)


def _two_port_expression(
    schema: SchemaFixture,
    arena: HigherSemanticArena,
) -> tuple[
    SchemaFixture,
    HigherSemanticArena,
    HigherExpressionID,
    HigherExpressionID,
    HigherExpressionID,
    HigherExpressionID,
]:
    primitive = schema.primitive
    state_sort = arena.state_sort(primitive, 0)
    left = arena.variable(state_sort, "simultaneous-left")
    right = arena.variable(state_sort, "simultaneous-right")
    symbol = arena.variable(arena.symbol_sort(primitive), "simultaneous-symbol")
    expression = arena.select(arena.equal_constant(symbol, 0), left, right)
    return schema, arena, left, right, symbol, expression


def _replacement_fixture() -> tuple[
    SchemaFixture,
    HigherSemanticArena,
    HigherExpressionID,
    HigherExpressionID,
    HigherExpressionID,
    HigherExpressionID,
    HigherExpressionID,
]:
    schema, arena = arena_fixture()
    _, arena, left, right, symbol, expression = _two_port_expression(schema, arena)
    literal = arena.literal(schema.primitive, 0, 1)
    return schema, arena, left, right, symbol, expression, literal


def _bound_replacement_fixture() -> tuple[
    SchemaFixture,
    HigherSemanticArena,
    HigherExpressionID,
    HigherExpressionID,
    HigherExpressionID,
    HigherExpressionID,
    HigherExpressionID,
    HigherExpressionID,
]:
    schema, arena, left, right, symbol, expression, literal = _replacement_fixture()
    bound = arena.bind_free_many(expression, ((left, right), (right, literal)))
    return schema, arena, left, right, symbol, expression, literal, bound


def test_simultaneous_binding_swaps_same_sort_ports() -> None:
    schema, arena = arena_fixture()
    _schema, arena, left, right, symbol, expression = _two_port_expression(
        schema, arena
    )
    bound = arena.bind_free_many(expression, ((left, right), (right, left)))

    for left_value, right_value, selected in ((0, 2, 0), (1, 2, 1)):
        actual = arena.evaluate(
            bound,
            {left: left_value, right: right_value, symbol: selected},
        )
        expected = arena.evaluate(
            expression,
            {left: right_value, right: left_value, symbol: selected},
        )
        assert actual == expected


def test_simultaneous_binding_replacements_share_original_environment() -> None:
    (
        _unused_schema_binding,
        arena,
        left,
        right,
        symbol,
        expression,
        _unused_literal_binding,
        bound,
    ) = _bound_replacement_fixture()

    for left_value, right_value, selected in ((0, 2, 0), (1, 2, 1)):
        actual = arena.evaluate(
            bound,
            {left: left_value, right: right_value, symbol: selected},
        )
        expected = arena.evaluate(
            expression,
            {left: right_value, right: 1, symbol: selected},
        )
        assert actual == expected


def test_simultaneous_binding_is_order_independent_and_warm_reuses_handle() -> None:
    _unused_schema_binding, arena, left, right, symbol, expression, literal, forward = (
        _bound_replacement_fixture()
    )
    before = len(arena.audit_snapshot().expressions)
    reverse = arena.bind_free_many(expression, ((right, literal), (left, right)))
    assert reverse == forward
    assert len(arena.audit_snapshot().expressions) == before
    warm = arena.bind_free_many(expression, ((left, right), (right, literal)))
    assert warm == forward
    assert len(arena.audit_snapshot().expressions) == before
    assert arena.evaluate(warm, {left: 0, right: 2, symbol: 0}) == 2


def test_sequential_rebind_keeps_its_defined_capture_semantics() -> None:
    _unused_schema_binding, arena, left, right, symbol, expression, literal = (
        _replacement_fixture()
    )
    sequential = arena.bind_free(
        arena.bind_free(expression, left, right), right, literal
    )
    simultaneous = arena.bind_free_many(
        expression,
        ((left, right), (right, literal)),
    )
    inputs = {left: 0, right: 2, symbol: 0}
    assert arena.evaluate(sequential, inputs) == 1
    assert arena.evaluate(simultaneous, inputs) == 2
    assert sequential != simultaneous


def test_unused_port_binding_is_a_noop_without_expression_nodes() -> None:
    schema, arena = arena_fixture()
    _schema, arena, _left, _right, _symbol, expression = _two_port_expression(
        schema, arena
    )
    unused = arena.variable(arena.state_sort(schema.primitive, 0), "unused")
    literal = arena.literal(schema.primitive, 0, 1)
    before = len(arena.audit_snapshot().expressions)
    checked = arena.ledger.counters.get("higher_simultaneous_binding_pairs_checked", 0)
    relevant = arena.ledger.counters.get("higher_simultaneous_binding_ports", 0)
    bound = arena.bind_free_many(expression, ((unused, literal),))
    assert bound is expression
    assert len(arena.audit_snapshot().expressions) == before
    assert (
        arena.ledger.counters["higher_simultaneous_binding_pairs_checked"]
        == checked + 1
    )
    assert arena.ledger.counters.get("higher_simultaneous_binding_ports", 0) == relevant


def test_simultaneous_binding_is_deferred_and_constant_size(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    schema, arena = arena_fixture()
    primitive = schema.primitive
    state_sort = arena.state_sort(primitive, 0)
    left = arena.variable(state_sort, "large-left")
    right = arena.variable(state_sort, "large-right")
    symbol = arena.variable(arena.symbol_sort(primitive), "large-symbol")
    expression = arena.select(arena.equal_constant(symbol, 0), left, right)
    for _ in range(1024):
        expression = arena.primitive_step(primitive, 0, expression, symbol)
    before = len(arena.audit_snapshot().expressions)
    evaluations = arena.metrics().evaluations

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("binding construction evaluated or rewrote the body")

    monkeypatch.setattr(arena, "evaluate", forbidden)
    monkeypatch.setattr(arena, "substitute", forbidden)
    bound = arena.bind_free_many(expression, ((left, right), (right, left)))
    monkeypatch.undo()
    assert bound != expression
    after = len(arena.audit_snapshot().expressions)
    assert after - before <= 6
    assert after < 3_000
    assert arena.metrics().evaluations == evaluations == 0


def test_simultaneous_binding_rejects_duplicate_foreign_and_wrong_sort_ports() -> None:
    schema, arena = arena_fixture()
    _schema, arena, left, right, symbol, expression = _two_port_expression(
        schema, arena
    )
    literal = arena.literal(schema.primitive, 0, 0)
    with pytest.raises(ValueError, match="repeat"):
        arena.bind_free_many(expression, ((left, literal), (left, right)))
    other_schema, _other_arena = arena_fixture()
    foreign = _other_arena.variable(
        _other_arena.state_sort(other_schema.primitive, 0), "foreign"
    )
    with pytest.raises(ValueError):
        arena.bind_free_many(expression, ((left, foreign),))
    with pytest.raises(ValueError, match="equal free-port sorts"):
        arena.bind_free_many(expression, ((left, symbol),))
    with pytest.raises(TypeError, match="immutable port vector"):
        arena.bind_free_many(
            expression,
            cast(
                tuple[tuple[HigherExpressionID, HigherExpressionID], ...],
                [(left, literal)],
            ),
        )


def test_spatial_bound_binds_right_dependent_left_replacement_simultaneously() -> None:
    (
        _actions,
        primitive,
        semantics,
        _runtime,
        _outputs,
        producer,
        _images,
        binding,
    ) = temporal_construction_fixture((9,))
    macro = producer.compile(binding)
    record = producer.interfaces.resolve(macro.interface)
    signature = producer.interfaces.interface(record.signature)
    ports = {port.role: port.variable for port in signature.inputs}
    assert ports.keys() == {"left-boundary", "right-boundary"}
    left_port, right_port = ports["left-boundary"], ports["right-boundary"]

    component = cast(HigherExpressionID, record.components.output)

    dependent_symbol = semantics.primitive_emit(
        primitive,
        producer.left,
        producer.symbol,
        producer.right,
    )
    left_replacement = semantics.primitive_step(
        primitive,
        0,
        producer.left,
        dependent_symbol,
    )
    right_replacement = semantics.literal(primitive, 1, 0)
    bind_component = cast(
        Callable[
            [LocalInterfaceID, str, HigherExpressionID, HigherExpressionID],
            HigherExpressionID,
        ],
        object.__getattribute__(producer, "_bound"),
    )
    bound = bind_component(
        macro.interface, "output", left_replacement, right_replacement
    )
    inputs = {producer.left: 0, producer.right: 1, producer.symbol: 18}
    replacement_values = {
        left_port: semantics.evaluate(left_replacement, inputs),
        right_port: semantics.evaluate(right_replacement, inputs),
    }
    expected = semantics.evaluate(component, replacement_values)
    assert semantics.evaluate(bound, inputs) == expected == 6
    old_sequential = semantics.bind_free(
        semantics.bind_free(component, left_port, left_replacement),
        right_port,
        right_replacement,
    )
    assert semantics.evaluate(old_sequential, inputs) == 18
