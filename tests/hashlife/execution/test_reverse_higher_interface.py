from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import fields
from typing import Never, cast

import pytest

from devtools.experiments.reverse_add.higher_interface import (
    ReverseHigherInterfaceCompilation,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    _Emit,
    _Initial,
    _Step,
)
from number_compiler.hashlife.execution.continuations.higher_interfaces import (
    HigherMacroComponents,
    HigherMacroInterface,
    HigherPort,
)
from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
    HigherSpatialMacroComposer,
    SourceBoundHigherMacro,
    _MacroBindingKey,
)
from number_compiler.hashlife.execution.continuations.higher_temporal_provider import (
    HigherTemporalProviderEvaluator,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    FieldAtomSort,
    FieldStateSort,
    HigherExpressionID,
)
from number_compiler.hashlife.execution.field_images import SourceForestID
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveCoordinateMorphismArena,
    RecursiveOutputSource,
    RecursiveOutputTemporal,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from tests.support.reverse_higher_interface import _direct_step
from tests.support.reverse_higher_runtime import _fixture


def test_reverse_leaf_activity_positions_use_harmless_zero_for_blank_and_active() -> (
    None
):
    (
        _actions,
        primitive,
        semantics,
        runtime,
        interfaces,
        compiler,
        _sources,
        _binding,
    ) = _fixture()
    compiled = compiler.compile(primitive)
    components = interfaces.resolve(compiled.interface).components
    left = semantics.evaluate(runtime.initial(primitive, 0))
    right = semantics.evaluate(runtime.initial(primitive, 1))
    for symbol in (7, 19):
        inputs = {compiled.left: left, compiled.symbol: symbol, compiled.right: right}
        assert semantics.evaluate(_expression(components.first_active), inputs) == 0
        assert semantics.evaluate(_expression(components.last_active), inputs) == 0


def test_reverse_schema_cache_cannot_be_entered_by_hash_equality_spoof() -> None:
    _actions, primitive, semantics, *_ = _fixture()
    schema = semantics.schema
    schema.validate_action(primitive)

    class Spoof:
        def __hash__(self) -> int:
            return hash(primitive)

        def __eq__(self, _other: object) -> bool:
            return True

    before = semantics.ledger.snapshot()
    with pytest.raises(TypeError, match="field-action ID"):
        schema.validate_action(cast("FieldCellActionID", Spoof()))
    assert semantics.ledger.snapshot() == before


def test_reverse_schema_readonly_validation_does_not_publish_cache_entries() -> None:
    from devtools.experiments.reverse_add.higher_schema import (
        ReverseHigherActionSchema,
    )

    actions, primitive, semantics, *_ = _fixture()
    action = actions.power(primitive, 3)
    before = semantics.ledger.snapshot()
    semantics._validate_sort(FieldStateSort(action, 0), readonly=True)
    assert semantics.ledger.snapshot() == before
    assert isinstance(semantics.schema, ReverseHigherActionSchema)
    assert action not in semantics.schema._children


@pytest.mark.parametrize(
    "steps,source",
    (
        (3, (7, 18, 7, 19, 19, 19, 19, 19)),
        (4, (7, 18, 7, 19, 19, 19, 19, 19)),
        (8, (7,)),
    ),
)
def test_reverse_higher_interface_nonbalanced_and_power_actions_are_exact(
    steps: int,
    source: tuple[int, ...],
) -> None:
    actions, primitive, semantics, runtime, interfaces, compiler, sources, binding = (
        _fixture(source)
    )
    action = actions.power(primitive, steps)
    compiled = compiler.compile(action)
    record = interfaces.resolve(compiled.interface)
    output = _expression(record.components.output)
    expected: tuple[int, ...] = source
    for _ in range(steps):
        expected = _direct_step(expected, 10)
    observed = tuple(
        runtime.point(action, binding, coordinate) for coordinate in range(len(source))
    )
    assert observed == expected

    coordinate = min(2, len(source) - 1)
    left = semantics.evaluate(runtime.boundary(action, binding, 0, 0, coordinate))
    right = semantics.evaluate(
        runtime.boundary(action, binding, 1, coordinate + 1, len(source)),
    )
    evaluated = semantics.evaluate(
        output,
        {
            compiled.left: left,
            compiled.symbol: sources.binding_read(binding, coordinate),
            compiled.right: right,
        },
    )
    assert evaluated == observed[coordinate]


def test_reverse_higher_interface_aliases_before_semantic_work_and_ignores_source() -> (
    None
):
    actions, primitive, semantics, _runtime, interfaces, compiler, sources, _binding = (
        _fixture()
    )
    # These are distinct source occurrences of the same immutable blank leaf.
    # The semantic compiler has no source argument, and therefore cannot split
    # the action identity by occurrence provenance.
    assert sources.intern(3, 0) == sources.intern(4, 0)
    first_action = actions.power(primitive, 4)
    alternate = actions.compose(
        actions.compose(primitive, primitive),
        actions.compose(primitive, primitive),
    )
    assert alternate == first_action
    first = compiler.compile(first_action)
    before = semantics.metrics()
    second = compiler.compile(alternate)
    assert second == first
    assert semantics.metrics() == before
    assert interfaces.resolve(first.interface).signature == first.signature
    assert all("source" not in field.name for field in fields(type(first)))


def test_reverse_higher_interface_distinguishes_complete_output_behavior() -> None:
    (
        actions,
        primitive,
        _semantics,
        _runtime,
        interfaces,
        compiler,
        _sources,
        _binding,
    ) = _fixture()
    t4, t8 = actions.power(primitive, 4), actions.power(primitive, 8)
    first, second = compiler.compile(t4), compiler.compile(t8)
    assert first.signature != second.signature
    assert first.interface != second.interface
    assert interfaces.resolve(first.interface).components.output != (
        interfaces.resolve(second.interface).components.output
    )


def test_reverse_higher_interface_records_have_no_future_or_proof_payloads() -> None:
    (
        actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        _sources,
        _binding,
    ) = _fixture()
    compiled = compiler.compile(actions.power(primitive, 8))
    interfaces.resolve(compiled.interface)
    forbidden = {
        "digits",
        "tile",
        "span",
        "carry_rows",
        "proof_state",
        "future",
        "coefficient",
        "source",
        "word",
        "slab",
        "cut",
    }
    for record in semantics._expressions:
        assert forbidden.isdisjoint(record.__dataclass_fields__)
    for function_record in semantics._functions:
        assert forbidden.isdisjoint(function_record.__dataclass_fields__)
    higher = interfaces.resolve(compiled.interface)
    assert all(
        type(component) is HigherExpressionID
        for component in higher.components.functions()
    )
    pending: list[object] = [interfaces.interface(compiled.signature).kernel.behavior]
    while pending:
        value = pending.pop()
        assert not isinstance(value, ArenaHandle)
        if type(value) is tuple:
            pending.extend(value)
        elif hasattr(value, "behavior"):
            pending.append(value.behavior)


def test_recursive_output_observes_one_branch_without_coordinate_tape() -> None:
    (
        _actions,
        primitive,
        semantics,
        runtime,
        interfaces,
        compiler,
        _sources,
        _binding,
    ) = _fixture()
    compiled = compiler.compile(primitive)
    local = interfaces.resolve(compiled.interface)
    signature = interfaces.interface(compiled.signature)

    def partial(symbol_value: int) -> LocalInterfaceID:
        symbol = semantics.symbol(primitive, symbol_value)
        components = HigherMacroComponents(
            *(
                semantics.substitute(_expression(component), compiled.symbol, symbol)
                for component in local.components.functions()
            )
        )
        contract = HigherMacroInterface(
            signature.kernel,
            (
                HigherPort(compiled.left, "left-boundary"),
                HigherPort(compiled.right, "right-boundary"),
            ),
            signature.outputs,
            signature.phase_count,
        )
        return interfaces.intern(interfaces.intern_interface(contract), components)

    first, second = partial(7), partial(18)
    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
    )
    left_leaf = outputs.leaf(first)
    right_leaf = outputs.leaf(second)
    parent = outputs.branch(left_leaf, right_leaf, first, second, 1)
    left = semantics.evaluate(runtime.initial(primitive, 0))
    right = semantics.evaluate(runtime.initial(primitive, 1))
    expected = _direct_step((7, 18), 10)
    assert (
        tuple(
            outputs.observe(parent, coordinate, left, right) for coordinate in range(2)
        )
        == expected
    )
    assert len(outputs._nodes) == 3
    assert all(not hasattr(record, "digits") for record in outputs._nodes.values())
    with pytest.raises((TypeError, ValueError)):
        outputs.resolve(cast(CoordinateOutputMorphismID, parent.local_id))


def test_temporal_output_normalizes_before_interning() -> None:
    (
        actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        _sources,
        _binding,
    ) = _fixture()
    interface = compiler.compile(primitive).interface
    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
        validate_action=actions.resolve,
        compose_actions=actions.compose,
        complete_temporal_action=lambda _provider, action: action,
    )
    source = outputs.leaf(interface)
    first = outputs.temporal(source, primitive, interface)
    result = outputs.temporal(first, primitive, interface)
    record = outputs.resolve(result)
    assert isinstance(record, RecursiveOutputTemporal)
    assert record.provider == source
    assert record.action == actions.compose(primitive, primitive)
    assert not isinstance(outputs.resolve(record.provider), RecursiveOutputTemporal)
    assert outputs.temporal(first, primitive, interface) == result
    assert len(outputs._nodes) == 3


def test_source_temporal_provider_is_canonical_before_boundary_binding() -> None:
    (
        actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        sources,
        binding,
    ) = _fixture((7,))
    source = sources.resolve_forest(binding).cells[0]
    interface = compiler.compile(primitive).interface
    observations: list[tuple[object, object]] = []

    def evaluate_temporal(
        _provider: CoordinateOutputMorphismID,
        _action: FieldCellActionID,
        _interface: LocalInterfaceID,
        coordinate: int,
        left: object,
        right: object,
    ) -> int:
        assert coordinate == 0
        observations.append((left, right))
        return 7

    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
        validate_action=actions.resolve,
        compose_actions=actions.compose,
        complete_temporal_action=lambda _provider, action: action,
        validate_source=sources.resolve,
        read_source=sources.symbol,
        evaluate_temporal=evaluate_temporal,
    )
    provider = outputs.source(source)
    assert isinstance(outputs.resolve(provider), RecursiveOutputSource)
    assert outputs.observe(provider, 0, 99, 101) == 7
    image = outputs.source_image(source, primitive, interface)
    assert outputs.source_image(source, primitive, interface) == image
    assert outputs.observe(image, 0, 0, 0) == 7
    assert outputs.observe(image, 0, 1, 2) == 7
    assert observations == [(0, 0), (1, 2)]
    assert outputs.resolve(image) == RecursiveOutputTemporal(
        provider,
        primitive,
        interface,
    )
    foreign_sources = _fixture((8,))[6]
    foreign = foreign_sources.resolve_forest(foreign_sources.forest(0, 1)).cells[0]
    before = len(outputs._nodes)
    with pytest.raises(ValueError, match="different arena"):
        outputs.source(foreign)
    assert len(outputs._nodes) == before


def test_temporal_output_validates_foreign_action_before_publication() -> None:
    (
        actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        _sources,
        _binding,
    ) = _fixture()
    foreign_actions, foreign, *_unused = _fixture((7, 18))
    assert foreign_actions is not actions
    interface = compiler.compile(primitive).interface
    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
        validate_action=actions.resolve,
        compose_actions=actions.compose,
        complete_temporal_action=lambda _provider, action: action,
    )
    source = outputs.leaf(interface)
    before = len(outputs._nodes)
    with pytest.raises(ValueError, match="different arena"):
        outputs.temporal(source, foreign, interface)
    assert len(outputs._nodes) == before


def test_higher_spatial_macro_composes_source_without_output_tape() -> None:
    (
        _actions,
        primitive,
        semantics,
        runtime,
        interfaces,
        compiler,
        sources,
        binding,
    ) = _fixture((7, 18, 7, 19, 19, 19, 19, 19))
    compiled = compiler.compile(primitive)
    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
    )
    composer = HigherSpatialMacroComposer(
        semantics,
        interfaces,
        outputs,
        sources,
        primitive,
        compiled.interface,
        compiled.left,
        compiled.symbol,
        compiled.right,
    )
    macro = composer.compile(binding)
    left = semantics.evaluate(runtime.initial(primitive, 0))
    right = semantics.evaluate(runtime.initial(primitive, 1))
    expected = _direct_step((7, 18, 7, 19, 19, 19, 19, 19), 10)
    assert (
        tuple(
            outputs.observe(macro.output, coordinate, left, right)
            for coordinate in range(macro.width)
        )
        == expected
    )
    assert len(outputs._nodes) < 2 * macro.width
    assert all(
        not hasattr(record, "digits") and not hasattr(record, "coordinate_values")
        for record in outputs._nodes.values()
    )


def test_reverse_macro_keeps_coordinate_magnitudes_outside_local_port_sorts() -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    (
        _actions,
        primitive,
        semantics,
        runtime,
        interfaces,
        compiler,
        sources,
        binding,
    ) = _fixture(source)
    compiled = compiler.compile(primitive)
    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
    )
    composer = HigherSpatialMacroComposer(
        semantics,
        interfaces,
        outputs,
        sources,
        primitive,
        compiled.interface,
        compiled.left,
        compiled.symbol,
        compiled.right,
    )
    macro = composer.compile(binding)
    record = interfaces.resolve(macro.interface)
    signature = interfaces.interface(record.signature)
    for role in ("first_active", "last_active", "extent", "growth"):
        sort = signature.outputs[
            tuple(HigherMacroComponents.__dataclass_fields__).index(role)
        ]
        assert type(sort) is FieldAtomSort
        assert sort.cardinality == 2
    shorter = composer.compile(sources.forest(0, 4))
    assert interfaces.resolve(shorter.interface).signature == record.signature

    ports = {port.role: port.variable for port in signature.inputs}
    left = semantics.evaluate(runtime.initial(primitive, 0))
    right = semantics.evaluate(runtime.initial(primitive, 1))
    extent = semantics.evaluate(
        macro.extent,
        {ports["left-boundary"]: left, ports["right-boundary"]: right},
    )
    expected = _direct_step(source, 10)
    assert (
        extent == max(index for index, value in enumerate(expected) if value != 19) + 1
    )


def test_reverse_macro_probes_the_source_parent_before_descending(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        sources,
        binding,
    ) = _fixture((7, 18, 7, 19, 19, 19, 19, 19))
    compiled = compiler.compile(primitive)
    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
    )
    composer = HigherSpatialMacroComposer(
        semantics,
        interfaces,
        outputs,
        sources,
        primitive,
        compiled.interface,
        compiled.left,
        compiled.symbol,
        compiled.right,
    )
    expected = composer.compile(binding)
    visits = semantics.ledger.counters.get("source_leaf_visits", 0)

    def forbidden(_source: object) -> Never:
        raise AssertionError("warm source parent descended into its children")

    monkeypatch.setattr(composer, "_cell", forbidden)
    assert composer.compile(binding) == expected
    assert semantics.ledger.counters.get("source_leaf_visits", 0) == visits
    assert semantics.ledger.counters["higher_spatial_forest_early_hits"] == 1


def test_reverse_macro_rejects_foreign_source_before_warm_binding_probe() -> None:
    (
        _actions,
        primitive,
        semantics,
        _runtime,
        interfaces,
        compiler,
        sources,
        binding,
    ) = _fixture((7, 18, 7, 19, 19, 19, 19, 19))
    compiled = compiler.compile(primitive)
    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
    )
    composer = HigherSpatialMacroComposer(
        semantics,
        interfaces,
        outputs,
        sources,
        primitive,
        compiled.interface,
        compiled.left,
        compiled.symbol,
        compiled.right,
    )
    composer.compile(binding)

    class PoisonedBindings(dict[_MacroBindingKey, SourceBoundHigherMacro]):
        def get(self, _key: object, _default: object = None) -> Never:
            raise AssertionError("invalid source reached the warm binding cache")

    composer._bindings = PoisonedBindings(composer._bindings)
    foreign = SourceForestID(
        ArenaToken("foreign-source"), binding.kind, binding.local_id
    )
    snapshot = semantics.ledger.snapshot()
    with pytest.raises(ValueError, match="different arena"):
        composer.compile(foreign)
    assert semantics.ledger.snapshot() == snapshot


def test_higher_operations_validate_scoped_ids_before_warm_cache_probe() -> None:
    (
        _actions,
        primitive,
        semantics,
        runtime,
        _interfaces,
        _compiler,
        _sources,
        _binding,
    ) = _fixture()
    state = runtime.initial(primitive, 0)
    symbol = semantics.symbol(primitive, 0)
    runtime.step(primitive, 0, state, symbol)

    class PoisonedOperations(dict[_Initial | _Step | _Emit, HigherExpressionID]):
        def get(self, _key: object, _default: object = None) -> Never:
            raise AssertionError("invalid scoped ID reached the operation cache")

    runtime._operations = PoisonedOperations(runtime._operations)
    foreign_action = FieldCellActionID(
        ArenaToken("foreign-action"),
        primitive.kind,
        primitive.local_id,
    )
    foreign_state = HigherExpressionID(
        ArenaToken("foreign-expression"),
        state.kind,
        state.local_id,
    )
    before = semantics.ledger.snapshot()
    with pytest.raises(ValueError, match="different arena"):
        runtime.initial(foreign_action, 0)
    with pytest.raises(ValueError, match="different arena"):
        runtime.step(primitive, 0, foreign_state, symbol)
    with pytest.raises(ValueError, match="different arena"):
        runtime.emit(primitive, foreign_state, symbol, state)
    assert semantics.ledger.snapshot() == before


def test_higher_temporal_provider_executes_without_midpoint_tile() -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    (
        actions,
        primitive,
        semantics,
        runtime,
        interfaces,
        compiler,
        sources,
        binding,
    ) = _fixture(source)
    compiled = compiler.compile(primitive)
    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
        validate_action=actions.resolve,
        compose_actions=actions.compose,
    )
    composer = HigherSpatialMacroComposer(
        semantics,
        interfaces,
        outputs,
        sources,
        primitive,
        compiled.interface,
        compiled.left,
        compiled.symbol,
        compiled.right,
    )
    macro = composer.compile(binding)
    evaluator = HigherTemporalProviderEvaluator(
        runtime,
        validate_output=outputs.resolve,
        compose_actions=actions.compose,
    )
    evaluator.bind(macro.output, binding, primitive)
    outputs.set_temporal_evaluator(
        evaluator,
        complete_action=evaluator.complete_action,
    )
    temporal = outputs.temporal(macro.output, primitive, macro.interface)
    composed = actions.compose(primitive, primitive)
    left = semantics.evaluate(runtime.initial(composed, 0))
    right = semantics.evaluate(runtime.initial(composed, 1))
    expected = _direct_step(_direct_step(source, 10), 10)
    compose_requests = actions.compose_requests
    assert (
        tuple(
            outputs.observe(temporal, coordinate, left, right)
            for coordinate in range(len(source))
        )
        == expected
    )
    assert actions.compose_requests == compose_requests
    assert all(
        not hasattr(record, "digits") and not hasattr(record, "source_tile")
        for record in outputs._nodes.values()
    )


def test_runtime_k_u_carrier_observes_power_without_syntax_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    actions, primitive, semantics, runtime, *_rest, binding = _fixture(source)
    expected: tuple[int, ...] = source
    expectations: dict[int, tuple[int, ...]] = {}
    for step in range(1, 17):
        expected = _direct_step(expected, 10)
        if step in (4, 8, 16):
            expectations[step] = expected

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("structural K/U observation reached syntax evaluation")

    monkeypatch.setattr(semantics, "evaluate", forbidden)
    monkeypatch.setattr(runtime, "point", forbidden)
    for steps, expected_word in expectations.items():
        action = actions.power(primitive, steps)
        assert runtime.point_structural(action, binding, 0) == expected_word[0]
    assert semantics.ledger.counters.get("higher_runtime_summary_publications", 0) > 0


def test_higher_compiler_payload_audit_rejects_integer_cache_key_alias() -> None:
    from devtools.experiments.reverse_add.temporal_payload_audit import (
        audit_reverse_temporal_experiment,
    )

    (
        _actions,
        primitive,
        _semantics,
        runtime,
        _interfaces,
        compiler,
        _sources,
        _binding,
    ) = _fixture()
    compiled = compiler.compile(primitive)
    storage_attribute = "_data"
    cache = cast(
        MutableMapping[object, ReverseHigherInterfaceCompilation],
        getattr(compiler._cache, storage_attribute),
    )
    del cache[primitive]
    cache[primitive.local_id] = compiled
    damaged = audit_reverse_temporal_experiment(runtime.ledger)
    assert damaged.invalid


def test_temporal_leaf_reuses_existing_complete_operation_before_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.experiments.reverse_add.temporal_leaf_diamond import (
        evaluate_temporal_leaf,
    )
    from number_compiler.hashlife.execution.continuations.higher_operations import (
        evaluate_operation,
    )

    actions, primitive, semantics, *_ = _fixture()
    action = actions.compose(primitive, primitive)
    left = evaluate_operation(semantics, "initial", action, 0, ())
    right = evaluate_operation(semantics, "initial", action, 1, ())
    expected = evaluate_operation(semantics, "emit", action, -1, (left, 7, right))
    before = semantics.ledger.snapshot()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("published parent was replayed")

    monkeypatch.setattr(semantics.schema, "children", forbidden)
    assert (
        evaluate_temporal_leaf(
            semantics,
            action,
            7,
            left,
            right,
            prefix_probe=forbidden,
        )
        == expected
    )
    after = semantics.ledger.snapshot()
    assert (before.entries, before.nodes) == (after.entries, after.nodes)
    assert after.counters["temporal_leaf_parent_hits"] == 1


def test_temporal_leaf_rejects_foreign_handle_before_semantic_memo() -> None:
    from devtools.experiments.reverse_add.temporal_leaf_diamond import (
        evaluate_temporal_leaf,
    )

    _, primitive, semantics, *_ = _fixture()
    _, foreign, _, *_ = _fixture()
    before = semantics.ledger.snapshot()
    with pytest.raises(ValueError):
        evaluate_temporal_leaf(semantics, foreign, 7, 0, 0)
    with pytest.raises(TypeError):
        evaluate_temporal_leaf(semantics, primitive, True, 0, 0)
    after = semantics.ledger.snapshot()
    assert (before.entries, before.nodes) == (after.entries, after.nodes)


@pytest.mark.parametrize("side", (0, 1))
def test_runtime_identity_transfer_is_erased_before_state_publication(
    side: int,
) -> None:
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        RuntimeUnarySummary,
        UnaryIdentity,
    )

    _, primitive, semantics, runtime, *_ = _fixture()
    summaries = runtime.summaries
    identity = summaries._intern(RuntimeUnarySummary(primitive, side, UnaryIdentity()))
    incoming = semantics.schema.initial(primitive, side)
    before = semantics.ledger.snapshot()
    assert summaries.transfer_value(identity, incoming) == incoming
    assert summaries.combine_runtime_unary((identity, identity)) == identity
    after = semantics.ledger.snapshot()
    assert (before.entries, before.nodes) == (after.entries, after.nodes)
    assert after.counters["higher_identity_transfer_elisions"] >= 2
    with pytest.raises(TypeError):
        summaries.transfer_value(identity, True)


def test_reverse_carry_reset_and_identity_do_not_erase_complete_output_state() -> None:
    """Carry-only aliases are not aliases of the complete two-sided machine."""
    actions, primitive, semantics, *_ = _fixture()
    schema = semantics.schema
    actions.validate_action(primitive)

    # Pair symbol zero resets the arithmetic carry, but the complete reverse
    # port also retains both directed suffix effects.  Those five admissible
    # states therefore do not collapse to one continuation.
    reset_map = tuple(
        schema.step(primitive, 1, state, 0)
        for state in range(schema.state_count(primitive, 1))
    )
    assert reset_map == (1, 1, 4, 1, 4)
    assert len(set(reset_map)) > 1
    assert schema.emit(primitive, 0, 0, 0) == 0
    assert schema.emit(primitive, 0, 0, 2) == 1

    # Symbols b-1 and blank induce the same identity boundary transfer on the
    # right port, yet their emitted symbols differ.  Canonicalizing a step
    # continuation from transfer behavior alone would merge unequal outputs.
    identity_nine = tuple(
        schema.step(primitive, 1, state, 9)
        for state in range(schema.state_count(primitive, 1))
    )
    identity_blank = tuple(
        schema.step(primitive, 1, state, 19)
        for state in range(schema.state_count(primitive, 1))
    )
    assert identity_nine == identity_blank == tuple(range(5))
    assert schema.emit(primitive, 0, 9, 0) == 18
    assert schema.emit(primitive, 0, 19, 0) == 19

    # Exhaust the complete primitive domain.  All twenty pair symbols have a
    # distinct joint (left transfer, right transfer, output) behavior even
    # though their carry-only transfer signatures occupy just three classes.
    left_count = schema.state_count(primitive, 0)
    right_count = schema.state_count(primitive, 1)
    complete_behaviors = {
        (
            tuple(
                schema.step(primitive, 0, state, symbol) for state in range(left_count)
            ),
            tuple(
                schema.step(primitive, 1, state, symbol) for state in range(right_count)
            ),
            tuple(
                schema.emit(primitive, left, symbol, right)
                for left in range(left_count)
                for right in range(right_count)
            ),
        )
        for symbol in range(20)
    }
    assert len(complete_behaviors) == 20


def _expression(value: ArenaHandle) -> HigherExpressionID:
    assert isinstance(value, HigherExpressionID)
    return value
