from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_interfaces import (
    HigherLocalInterfaceArena,
    HigherMacroComponents,
    HigherMacroInterface,
    HigherPort,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    FieldAtomSort,
    HigherExpressionID,
    HigherFunctionID,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeAtom,
    RuntimeValueID,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    LocalInterfaceID,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.assertions import assert_no_forbidden_dataclass_fields


@dataclass
class SchemaFixture:
    ledger: ResourceLedger

    def __post_init__(self) -> None:
        self.owner = ArenaToken("higher-test-actions")
        self.identity = self.scoped_handle(0)
        self.primitive = self.scoped_handle(1)
        self.second = self.scoped_handle(2)
        self.t2 = self.scoped_handle(3)
        self.t4 = self.scoped_handle(4)
        self._children = {
            3: (self.primitive, self.second),
            4: (self.t2, self.t2),
        }

    def scoped_handle(self, local_id: int) -> FieldCellActionID:
        return FieldCellActionID(self.owner, "field-cell-action", local_id)

    def validate_action(self, action: FieldCellActionID) -> None:
        if type(action) is not FieldCellActionID:
            raise TypeError("expected a field action")
        action.validate(self.owner, "field-cell-action", size=5)

    def children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        self.validate_action(action)
        return self._children.get(action.local_id)

    def kind(
        self, action: FieldCellActionID
    ) -> Literal["identity", "primitive", "compose"]:
        self.validate_action(action)
        if action.local_id == 0:
            return "identity"
        return "compose" if action.local_id in self._children else "primitive"

    def alphabet(self, action: FieldCellActionID) -> tuple[int, int]:
        self.validate_action(action)
        return 2, 2

    def state_count(self, action: FieldCellActionID, side: int) -> int:
        self.validate_action(action)
        if type(side) is not int or side not in (0, 1):
            raise ValueError(side)
        return 1 if action.local_id == 0 else 3

    def initial(self, action: FieldCellActionID, side: int) -> int:
        self.validate_action(action)
        if type(side) is not int or side not in (0, 1):
            raise ValueError(side)
        return 0

    def step(
        self, action: FieldCellActionID, side: int, state: int, symbol: int
    ) -> int:
        self.validate_action(action)
        if action.local_id == 1:
            return (state + 1) % 3 if symbol == 0 else (2 * state) % 3
        return (state + symbol + side + 1) % 3

    def emit(
        self,
        action: FieldCellActionID,
        left: int,
        symbol: int,
        right: int,
    ) -> int:
        self.validate_action(action)
        return (left + symbol + 2 * right + action.local_id) % 3


def arena_fixture() -> tuple[SchemaFixture, HigherSemanticArena]:
    schema = SchemaFixture(ResourceLedger())
    return schema, HigherSemanticArena(schema)


def test_substitution_preserves_variable_dependency_identity() -> None:
    schema, arena = arena_fixture()
    symbol = arena.variable(arena.symbol_sort(schema.primitive), "symbol")
    state = arena.variable(arena.state_sort(schema.primitive, 0), "state", (symbol,))
    expression = arena.primitive_step(schema.primitive, 0, state, symbol)
    zero = arena.symbol(schema.primitive, 0)

    replaced = arena.substitute(expression, symbol, zero)

    # Dependency children distinguish variable identities; they are not free
    # occurrences inside that variable. Only the explicit symbol is replaced.
    assert replaced == arena.primitive_step(schema.primitive, 0, state, zero)
    assert arena.free_variables(replaced) == (state,)
    assert arena.evaluate(replaced, {state: 1}) == schema.step(
        schema.primitive, 0, 1, 0
    )


def test_substitution_keeps_occurrences_inside_replacement_free() -> None:
    schema, arena = arena_fixture()
    state = arena.variable(arena.state_sort(schema.primitive, 0), "state")
    zero = arena.symbol(schema.primitive, 0)
    expression = arena.primitive_step(schema.primitive, 0, state, zero)
    replaced = arena.substitute(expression, state, expression)
    assert replaced == arena.primitive_step(schema.primitive, 0, expression, zero)
    assert arena.free_variables(replaced) == (state,)
    assert arena.evaluate(replaced, {state: 0}) == 2


def test_substitution_reaches_free_symbol_under_function_binder() -> None:
    schema, arena = arena_fixture()
    parameter = arena.variable(arena.state_sort(schema.primitive, 0), "parameter")
    symbol = arena.variable(arena.symbol_sort(schema.primitive), "symbol")
    body = arena.primitive_step(schema.primitive, 0, parameter, symbol)
    function = arena.function_expression(arena.function(parameter, body))
    replaced = arena.substitute(function, symbol, arena.symbol(schema.primitive, 0))
    assert not arena.free_variables(replaced)
    assert (
        arena.evaluate(arena.apply(replaced, arena.literal(schema.primitive, 0, 1)))
        == 2
    )


def test_substitution_reaches_deferred_binding_replacement() -> None:
    schema, arena = arena_fixture()
    state = arena.literal(schema.primitive, 0, 1)
    symbol = arena.variable(arena.symbol_sort(schema.primitive), "symbol")
    replacement = arena.variable(arena.symbol_sort(schema.primitive), "replacement")
    expression = arena.primitive_step(schema.primitive, 0, state, symbol)
    bound = arena.bind_free(expression, symbol, replacement)
    replaced = arena.substitute(bound, replacement, arena.symbol(schema.primitive, 0))
    assert not arena.free_variables(replaced)
    assert arena.evaluate(replaced) == 2
    assert arena.substitute(bound, symbol, arena.symbol(schema.primitive, 1)) == bound


def test_higher_identity_and_noncommuting_primitive_order() -> None:
    schema, arena = arena_fixture()
    assert arena.evaluate(arena.literal(schema.identity, 0, 0)) == 0
    state = arena.literal(schema.primitive, 0, 1)
    zero = arena.symbol(schema.primitive, 0)
    one = arena.symbol(schema.primitive, 1)
    add_then_double = arena.primitive_step(
        schema.primitive,
        0,
        arena.primitive_step(schema.primitive, 0, state, zero),
        one,
    )
    double_then_add = arena.primitive_step(
        schema.primitive,
        0,
        arena.primitive_step(schema.primitive, 0, state, one),
        zero,
    )
    assert arena.evaluate(add_then_double) == 1
    assert arena.evaluate(double_then_add) == 0


def test_higher_functions_are_alpha_canonical_and_beta_reduce() -> None:
    schema, arena = arena_fixture()
    sort = arena.state_sort(schema.primitive, 0)
    x, y = arena.variable(sort, "x"), arena.variable(sort, "y")
    symbol = arena.symbol(schema.primitive, 0)
    first = arena.function(
        x,
        arena.primitive_step(schema.primitive, 0, x, symbol),
    )
    second = arena.function(
        y,
        arena.primitive_step(schema.primitive, 0, y, symbol),
    )
    assert first == second
    argument = arena.literal(schema.primitive, 0, 2)
    applied = arena.apply(arena.function_expression(first), argument)
    assert arena.evaluate(applied) == 0


def test_deferred_free_binding_is_constant_size_and_exact() -> None:
    schema, arena = arena_fixture()
    sort = arena.state_sort(schema.primitive, 0)
    variable = arena.variable(sort, "deferred-port")
    symbol = arena.symbol(schema.primitive, 0)
    expression = arena.primitive_step(schema.primitive, 0, variable, symbol)
    replacement = arena.literal(schema.primitive, 0, 2)
    before = len(arena.audit_snapshot().expressions)
    bound = arena.bind_free(expression, variable, replacement)
    assert len(arena.audit_snapshot().expressions) == before + 1
    assert arena.expression(bound).kind == "bind-free"
    assert arena.evaluate(bound) == arena.evaluate(expression, {variable: 2})
    assert arena.component_free_variables(bound) == ()


def test_identity_free_binding_is_normalized_before_publication() -> None:
    schema, arena = arena_fixture()
    sort = arena.state_sort(schema.primitive, 0)
    variable = arena.variable(sort, "shared-macro-port")
    symbol = arena.symbol(schema.primitive, 0)
    expression = arena.primitive_step(schema.primitive, 0, variable, symbol)
    before = len(arena.audit_snapshot().expressions)
    assert arena.bind_free(expression, variable, variable) == expression
    assert len(arena.audit_snapshot().expressions) == before


def test_bounded_scalar_identities_fold_before_publication() -> None:
    _schema, arena = arena_fixture()
    small = FieldAtomSort("small-coordinate", 4)
    large = FieldAtomSort("large-coordinate", 16)
    variable = arena.variable(small, "coordinate")
    widened = arena.retag(arena.retag(variable, large), large)
    assert widened == arena.retag(variable, large)
    assert arena.add_constant(widened, 0, large) == widened
    true = arena.constant(FieldAtomSort("boolean", 2), 1)
    assert arena.select(true, widened, arena.constant(large, 0)) == widened


def test_higher_select_evaluates_only_the_selected_branch() -> None:
    schema, arena = arena_fixture()
    sort = arena.state_sort(schema.primitive, 0)
    unreachable = arena.variable(sort, "poisoned-unbound-branch")
    selected = arena.literal(schema.primitive, 0, 2)
    condition = arena.constant(FieldAtomSort("boolean", 2), 1)
    assert arena.evaluate(arena.select(condition, selected, unreachable)) == 2


def test_higher_runtime_values_are_canonical_and_stale_safe() -> None:
    schema, arena = arena_fixture()
    parameter = arena.variable(arena.state_sort(schema.primitive, 0), "runtime-x")
    expression = arena.function_expression(arena.function(parameter, parameter))
    first = arena.evaluate(expression)
    second = arena.evaluate(expression)
    assert type(first) is RuntimeValueID and first == second
    arena.runtime_values.clear()
    with pytest.raises(ValueError, match="stale higher runtime value"):
        arena.runtime_values.resolve(first)


def test_higher_expression_publication_is_atomic_at_zero_budget() -> None:
    schema = SchemaFixture(ResourceLedger(max_cache_entries=0))
    arena = HigherSemanticArena(schema)
    with pytest.raises(BlockContextBudgetExceeded):
        arena.literal(schema.primitive, 0, 0)
    snapshot = arena.audit_snapshot()
    assert not snapshot.expressions
    assert not snapshot.expression_keys
    assert not snapshot.expression_free_ids


def test_higher_primitive_refuses_unbounded_state_enumeration() -> None:
    schema, arena = arena_fixture()

    def unbounded_state_count(_action: FieldCellActionID, _side: int) -> int:
        return 2**64

    object.__setattr__(schema, "state_count", unbounded_state_count)
    state = arena.variable(arena.state_sort(schema.primitive, 0), "large-state")
    symbol = arena.symbol(schema.primitive, 0)
    with pytest.raises(ValueError, match="bounded interface"):
        arena.primitive_step(schema.primitive, 0, state, symbol)


def test_higher_t2_and_t4_state_sorts_remain_structured() -> None:
    schema, arena = arena_fixture()
    anchor = arena.literal(schema.primitive, 0, 1)
    opposite = arena.variable(arena.state_sort(schema.primitive, 1), "opposite")
    target = arena.literal(schema.second, 0, 2)
    continuation = arena.function(opposite, target)
    t2 = arena.pair(schema.t2, 0, anchor, continuation)
    assert arena.evaluate(arena.anchor(t2)) == 1
    observed = arena.apply(
        arena.continuation(t2),
        arena.literal(schema.primitive, 1, 0),
    )
    assert arena.evaluate(observed) == 2

    t2_anchor = t2
    t2_opposite = arena.variable(arena.state_sort(schema.t2, 1), "t2-opposite")
    t2_target = arena.pair(schema.t2, 0, anchor, continuation)
    t4_continuation = arena.function(t2_opposite, t2_target)
    t4 = arena.pair(schema.t4, 0, t2_anchor, t4_continuation)
    assert arena.expression(t4).sort == arena.state_sort(schema.t4, 0)
    assert arena.evaluate(arena.anchor(arena.anchor(t4))) == 1
    initial_t4 = arena.initial(schema.t4, 0)
    assert arena.expression(initial_t4).sort == arena.state_sort(schema.t4, 0)
    assert arena.evaluate(arena.anchor(arena.anchor(initial_t4))) == 0


def test_higher_nested_continuation_preserves_outer_port_dependency() -> None:
    schema, arena = arena_fixture()
    outer = arena.variable(arena.state_sort(schema.primitive, 0), "outer")
    inner = arena.variable(arena.state_sort(schema.primitive, 1), "inner")
    source = arena.symbol(schema.primitive, 0)
    right = arena.literal(schema.primitive, 1, 0)
    emitted = arena.primitive_emit(schema.primitive, outer, source, right)
    target = arena.primitive_step(
        schema.second,
        0,
        arena.literal(schema.second, 0, 0),
        emitted,
    )
    continuation = arena.function(inner, target)
    pair = arena.pair(schema.t2, 0, outer, continuation)
    outer_function = arena.function(outer, pair)
    bound_pair = arena.apply(
        arena.function_expression(outer_function),
        arena.literal(schema.primitive, 0, 2),
    )
    observed = arena.apply(
        arena.continuation(bound_pair),
        arena.literal(schema.primitive, 1, 1),
    )
    expected_symbol = schema.emit(schema.primitive, 2, 0, 0)
    assert arena.evaluate(observed) == schema.step(schema.second, 0, 0, expected_symbol)


def test_higher_handles_reject_foreign_integer_bool_and_wrong_sort() -> None:
    schema, arena = arena_fixture()
    value = arena.literal(schema.primitive, 0, 0)
    function = arena.function(
        arena.variable(arena.state_sort(schema.primitive, 0), "x"),
        value,
    )
    before = arena.metrics()
    invalid = (
        value.local_id,
        True,
        HigherExpressionID(ArenaToken("foreign"), value.kind, value.local_id),
        HigherFunctionID(value.owner, "higher-semantic-function", value.local_id),
    )
    for reference in invalid:
        with pytest.raises((TypeError, ValueError)):
            arena.expression(cast(HigherExpressionID, reference))
    with pytest.raises((TypeError, ValueError)):
        arena.function_record(cast(HigherFunctionID, value))
    assert (
        arena.function_record(function).signature.codomain
        == arena.expression(value).sort
    )
    assert arena.metrics() == before


def test_higher_records_contain_no_exact_future_payloads() -> None:
    _unused_schema_binding, arena = _issued_records()
    forbidden = {"digits", "tile", "span", "carry_rows", "future", "coefficient"}
    snapshot = arena.audit_snapshot()
    assert_no_forbidden_dataclass_fields(
        forbidden,
        (record.__dataclass_fields__ for record in snapshot.expressions),
        (function.__dataclass_fields__ for function in snapshot.functions),
    )


def test_higher_payload_audit_validates_issued_records_and_rejects_mutation() -> None:
    from dataclasses import replace

    from number_compiler.resources.payload_audit import audit_registered_payloads

    _unused_schema_binding, arena = _issued_records()
    assert audit_registered_payloads(arena.ledger).forbidden_future_payloads == 0
    assert audit_registered_payloads(arena.ledger).unknown_payloads == 0

    store = arena.audit_snapshot().expression_store
    original = arena.audit_snapshot().expressions[0]
    expressions = cast(dict[int, object], object.__getattribute__(store, "_data"))
    expressions[0] = replace(original, value=1 << 65)
    damaged = audit_registered_payloads(arena.ledger)
    assert damaged.forbidden_future_payloads > 0


def test_higher_local_interface_publishes_typed_components_without_integer_encoding() -> (
    None
):
    schema, semantics = arena_fixture()
    value = semantics.variable(semantics.state_sort(schema.t4, 0), "left-state")
    interface = HigherMacroInterface(
        SemanticIdentity("higher-test-v1", ("complete", "t4")),
        (HigherPort(value, "left-state"),),
        (semantics.component_sort(value),) * 13,
    )
    arena = HigherLocalInterfaceArena(semantics)
    signature = arena.intern_interface(interface)
    components = HigherMacroComponents(*(value for _ in range(13)))
    quotient = arena.intern(signature, components)
    assert arena.intern(signature, components) == quotient
    assert arena.resolve(quotient).components == components
    assert all(type(item) is HigherExpressionID for item in components.functions())
    with pytest.raises((TypeError, ValueError)):
        arena.resolve(cast(LocalInterfaceID, quotient.local_id))
    foreign = HigherExpressionID(ArenaToken("foreign"), value.kind, value.local_id)
    bad = HigherMacroComponents(foreign, *(value for _ in range(12)))
    with pytest.raises((TypeError, ValueError)):
        arena.intern(signature, bad)

    # The base-class stores exist only for compatibility.  They use distinct
    # sorts, so a same-owner/local-ID handle cannot alias a higher record.
    forged_base_signature = PortSignatureID(
        arena.owner,
        "diamond-semantic-signature",
        signature.local_id,
    )
    forged_base_interface = LocalInterfaceID(
        arena.owner,
        "diamond-quotient",
        quotient.local_id,
    )
    with pytest.raises(ValueError):
        arena.interface(forged_base_signature)
    with pytest.raises(ValueError):
        arena.resolve(forged_base_interface)


def test_semantic_work_counts_deep_frames_even_when_observation_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    schema, arena = arena_fixture()
    source = arena.variable(arena.state_sort(schema.primitive, 0), "frame-source")
    expression = source
    symbol = arena.symbol(schema.primitive, 0)
    for _ in range(40):
        expression = arena.primitive_step(schema.primitive, 0, expression, symbol)
    original = arena.runtime_values.publish_evaluation
    calls = 0

    def fail_midway(expression: int, environment: int, value: RuntimeAtom) -> None:
        nonlocal calls
        calls += 1
        if calls == 20:
            raise RuntimeError("stop observation after actual work")
        return original(expression, environment, value)

    monkeypatch.setattr(arena.runtime_values, "publish_evaluation", fail_midway)
    with pytest.raises(RuntimeError, match="after actual work"):
        arena.evaluate(expression, {source: 0})
    assert calls == 20
    assert schema.ledger.counters["higher_semantic_task_frames"] > 40
    assert schema.ledger.counters.get("higher_semantic_evaluations", 0) == 0


def _issued_records() -> tuple[SchemaFixture, HigherSemanticArena]:
    schema, arena = arena_fixture()
    state = arena.literal(schema.primitive, 0, 0)
    symbol = arena.symbol(schema.primitive, 0)
    arena.primitive_step(schema.primitive, 0, state, symbol)
    return schema, arena
