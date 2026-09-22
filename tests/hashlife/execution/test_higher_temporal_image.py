from __future__ import annotations

from dataclasses import replace
from typing import Never

import pytest

from devtools.experiments.reverse_add.field_action import ReverseFieldActionArena
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
    HigherSpatialMacroComposer,
    SourceBoundHigherMacro,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_temporal_image import (
    HigherTemporalImageArena,
    HigherTemporalImageID,
)
from number_compiler.hashlife.execution.continuations.higher_temporal_provider import (
    HigherTemporalProviderEvaluator,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
)
from number_compiler.hashlife.execution.field_images import SourceForestID
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveCoordinateMorphismArena,
    RecursiveOutputTemporal,
)
from number_compiler.resources.higher_payload_audit import audit_higher_payloads
from number_compiler.resources.stores import LedgerDict
from tests.support.reverse_higher_runtime import _fixture


def _bound_step(
    word: tuple[int, ...],
    left_index: int,
    right_index: int,
    base: int = 10,
) -> tuple[int, ...]:
    effect = BaseBlockEffect(base)
    left_domain = tuple(effect.boundary_universe(BoundarySide.LEFT) or ())
    right_domain = tuple(effect.boundary_universe(BoundarySide.RIGHT) or ())
    left_states = []
    state = left_domain[left_index]
    for symbol in word:
        left_states.append(state)
        state = effect.advance(BoundarySide.LEFT, state, symbol)
    right_states = [right_domain[right_index]] * len(word)
    state = right_domain[right_index]
    for index in range(len(word) - 1, -1, -1):
        right_states[index] = state
        state = effect.advance(BoundarySide.RIGHT, state, word[index])
    return tuple(
        effect.emit(left_states[index], symbol, right_states[index])
        for index, symbol in enumerate(word)
    )


def _bound_exits(
    word: tuple[int, ...], left_index: int, right_index: int, base: int = 10
) -> tuple[int, int]:
    effect = BaseBlockEffect(base)
    left_domain = tuple(effect.boundary_universe(BoundarySide.LEFT) or ())
    right_domain = tuple(effect.boundary_universe(BoundarySide.RIGHT) or ())
    left = left_domain[left_index]
    for symbol in word:
        left = effect.advance(BoundarySide.LEFT, left, symbol)
    right = right_domain[right_index]
    for symbol in reversed(word):
        right = effect.advance(BoundarySide.RIGHT, right, symbol)
    return left_domain.index(left), right_domain.index(right)


def _construction(
    source: tuple[int, ...],
) -> tuple[
    ReverseFieldActionArena,
    FieldCellActionID,
    HigherSemanticArena,
    HigherBimachineRuntime,
    RecursiveCoordinateMorphismArena,
    HigherSpatialMacroComposer,
    HigherTemporalImageArena,
    SourceForestID,
]:
    actions, primitive, semantics, runtime, interfaces, compiler, sources, binding = (
        _fixture(source)
    )
    compiled = compiler.compile(primitive)
    outputs = RecursiveCoordinateMorphismArena(
        interfaces,
        evaluate=semantics.evaluate,
    )
    producer = HigherSpatialMacroComposer(
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
    consumer = HigherSpatialMacroComposer(
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

    images = HigherTemporalImageArena(
        consumer,
        compose_actions=actions.compose,
    )
    return (
        actions,
        primitive,
        semantics,
        runtime,
        outputs,
        producer,
        images,
        binding,
    )


def test_temporal_image_repeatedly_substitutes_bound_recursive_output(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    (
        _actions,
        primitive,
        semantics,
        runtime,
        outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    left = runtime.initial(primitive, 0)
    right = runtime.initial(primitive, 1)
    initial = images.bind_initial(
        producer, binding, producer.compile(binding), left, right
    )

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("temporal image construction reached evaluator fallback")

    monkeypatch.setattr(outputs, "temporal", forbidden)
    second = images.step(initial, left, right)
    third = images.step(second, left, right)
    expected_second = _bound_step(_bound_step(source, 0, 0), 0, 0)
    expected_third = _bound_step(expected_second, 0, 0)
    for image, expected in ((second, expected_second), (third, expected_third)):
        record = images.resolve(image)
        assert (
            tuple(
                outputs.observe(record.macro.output, coordinate, 0, 0)
                for coordinate in range(record.padded_extent)
            )
            == expected
        )
        assert all(
            type(node) is not RecursiveOutputTemporal
            for node in outputs._nodes.values()
        )
    assert semantics.ledger.counters["higher_temporal_image_node_visits"] > 0
    assert semantics.ledger.counters["higher_temporal_image_boundary_substitutions"] > 0


@pytest.mark.parametrize(
    "field",
    (
        "action",
        "local_interface",
        "left",
        "symbol",
        "right",
        "blank",
        "kernel_digest",
        "source_backed_temporal",
        "morphism_sort",
    ),
)
def test_temporal_memo_rejects_changed_consumer_before_a_warm_hit(
    field: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    actions, _primitive, semantics, _runtime, _outputs, _producer, images, _binding = (
        _construction((7, 19, 19, 19))
    )
    changes = {
        "action": actions.identity,
        "local_interface": None,
        "left": images.spatial.right,
        "symbol": images.spatial.left,
        "right": images.spatial.left,
        "blank": 0,
        "kernel_digest": "another-kernel",
        "source_backed_temporal": True,
        "morphism_sort": None,
    }
    try:
        first = images._blank_macro(4)
        before = dict(semantics.ledger.counters)
        with monkeypatch.context() as patch:
            patch.setattr(images.spatial, field, changes[field])
            with pytest.raises(ValueError, match="consumer binding"):
                images._blank_macro(4)
            assert dict(semantics.ledger.counters) == before
        assert images._blank_macro(4) is first
    finally:
        images._clear_workspace()
    assert not images._built and not images._frames
    assert images.ledger._account(images._built_owner).entries == 0
    assert images.ledger._account(images._frame_owner).entries == 0


def test_temporal_memo_keys_bind_consumer_and_reject_foreign_publication() -> None:
    actions, _primitive, _semantics, _runtime, _outputs, _producer, images, _binding = (
        _construction((7, 19, 19, 19))
    )
    try:
        macro = images._blank_macro(4)
        key = next(key for key in images._built if key.width == 4)
        foreign = replace(key, consumer=replace(key.consumer, action=actions.identity))
        assert key != foreign
        before = images.ledger._account(images._built_owner).entries
        with pytest.raises(ValueError, match="another consumer"):
            images._remember_built(foreign, macro)
        assert images.ledger._account(images._built_owner).entries == before
        assert foreign not in images._built
    finally:
        images._clear_workspace()


def test_temporal_step_work_and_results_are_not_reused_from_an_earlier_call() -> None:
    source = (7, 18, 7, *(19 for _ in range(29)))
    _actions, primitive, semantics, runtime, outputs, producer, images, binding = (
        _construction(source)
    )
    left, right = runtime.initial(primitive, 0), runtime.initial(primitive, 1)
    image = images.bind_initial(
        producer, binding, producer.compile(binding), left, right
    )
    expected = _bound_step(source, 0, 0)
    for _ in range(15):
        before = semantics.ledger.counters.get("higher_temporal_image_node_visits", 0)
        probes = semantics.ledger.counters.get(
            "higher_temporal_image_workspace_probes", 0
        )
        image = images.step(image, left, right)
        assert semantics.ledger.counters["higher_temporal_image_node_visits"] > before
        assert (
            semantics.ledger.counters["higher_temporal_image_workspace_probes"] > probes
        )
        assert not images._built and not images._frames
        assert images.ledger._account(images._built_owner).entries == 0
        expected = _bound_step(expected, 0, 0)
        record = images.resolve(image)
        assert (
            tuple(
                outputs.observe(record.macro.output, i, 0, 0)
                for i in range(record.padded_extent)
            )
            == expected
        )


def test_temporal_arena_rejects_replaced_composition_authority(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _actions,
        _primitive,
        _semantics,
        _runtime,
        _outputs,
        _producer,
        images,
        _binding,
    ) = _construction((7, 19, 19, 19))
    monkeypatch.setattr(images, "_compose_actions", lambda before, _after: before)
    with pytest.raises(ValueError, match="issued authority"):
        images._blank_macro(4)
    assert not images._built


def test_empty_temporal_arena_audit_rejects_changed_consumer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    actions, _primitive, _semantics, _runtime, _outputs, _producer, images, _binding = (
        _construction((7, 19, 19, 19))
    )
    assert not audit_higher_payloads(images.ledger).invalid
    monkeypatch.setattr(images.spatial, "action", actions.identity)
    assert audit_higher_payloads(images.ledger).invalid


@pytest.mark.parametrize(
    ("field", "value"), (("blank", 19.0), ("source_backed_temporal", 0))
)
def test_temporal_consumer_rejects_equal_but_differently_typed_fields(
    field: str, value: object, monkeypatch: pytest.MonkeyPatch
) -> None:
    (
        _actions,
        _primitive,
        _semantics,
        _runtime,
        _outputs,
        _producer,
        images,
        _binding,
    ) = _construction((7, 19, 19, 19))
    try:
        images._blank_macro(4)
        monkeypatch.setattr(images.spatial, field, value)
        with pytest.raises(ValueError, match="consumer binding"):
            images._blank_macro(4)
    finally:
        images._clear_workspace()


def test_temporal_consumer_seal_is_independent_of_the_memo_key(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _actions,
        _primitive,
        _semantics,
        _runtime,
        _outputs,
        _producer,
        images,
        _binding,
    ) = _construction((7, 19, 19, 19))
    try:
        images._blank_macro(4)
        object.__setattr__(images._consumer, "blank", 0)
        monkeypatch.setattr(images.spatial, "blank", 0)
        with pytest.raises(ValueError, match="consumer binding"):
            images._blank_macro(4)
    finally:
        images._clear_workspace()


def test_temporal_image_preserves_noninitial_two_sided_ports() -> None:
    source = (0, 1, 19, 19, 19, 19, 19, 19)
    (
        _actions,
        primitive,
        semantics,
        _runtime,
        outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    provider_left = semantics.literal(primitive, 0, 1)
    provider_right = semantics.literal(primitive, 1, 1)
    consumer_left = semantics.literal(primitive, 0, 2)
    consumer_right = semantics.literal(primitive, 1, 1)
    initial = images.bind_initial(
        producer,
        binding,
        producer.compile(binding),
        provider_left,
        provider_right,
    )
    result = images.resolve(images.step(initial, consumer_left, consumer_right))
    first = _bound_step(source, 1, 1)
    expected = _bound_step(first, 2, 1)
    assert (
        tuple(
            outputs.observe(result.macro.output, coordinate, 2, 1)
            for coordinate in range(result.padded_extent)
        )
        == expected
    )


def test_temporal_image_rejects_foreign_mutated_and_unbound_occurrences() -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    (
        _actions,
        primitive,
        _semantics,
        runtime,
        _outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    left = runtime.initial(primitive, 0)
    right = runtime.initial(primitive, 1)
    macro = producer.compile(binding)
    image = images.bind_initial(producer, binding, macro, left, right)
    foreign = HigherTemporalImageID(ArenaToken("foreign"), image.kind, image.local_id)
    with pytest.raises(ValueError, match="different arena"):
        images.resolve(foreign)

    record = images._nodes[image.local_id]
    object.__setattr__(record, "active_extent", record.active_extent - 1)
    with pytest.raises(ValueError, match="seal"):
        images.resolve(image)
    object.__setattr__(record, "active_extent", record.active_extent + 1)

    producer.clear()
    with pytest.raises(ValueError, match="not bound"):
        images.bind_initial(producer, binding, macro, left, right)


def test_temporal_image_rejects_unadmitted_growth_before_traversal() -> None:
    source = (7, 18, 7, 7)
    (
        _actions,
        primitive,
        semantics,
        runtime,
        _outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    left = runtime.initial(primitive, 0)
    right = runtime.initial(primitive, 1)
    initial = images.bind_initial(
        producer, binding, producer.compile(binding), left, right
    )
    before = semantics.ledger.counters.get("higher_temporal_image_node_visits", 0)
    with pytest.raises(ValueError, match="padding"):
        images.step(initial, left, right)
    assert (
        semantics.ledger.counters.get("higher_temporal_image_node_visits", 0) == before
    )
    assert not images._frames and not images._built


def test_temporal_image_growth_uses_one_admitted_blank_seam() -> None:
    source = (18, 18, 19, 19, 19, 19, 19, 19)
    (
        _actions,
        primitive,
        _semantics,
        runtime,
        outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    left = runtime.initial(primitive, 0)
    right = runtime.initial(primitive, 1)
    first_expected = _bound_step(source, 0, 0)
    assert next(index for index, value in enumerate(first_expected) if value == 19) > 2
    initial = images.bind_initial(
        producer, binding, producer.compile(binding), left, right
    )
    result = images.resolve(images.step(initial, left, right))
    expected = _bound_step(first_expected, 0, 0)
    assert (
        tuple(
            outputs.observe(result.macro.output, coordinate, 0, 0)
            for coordinate in range(result.padded_extent)
        )
        == expected
    )
    assert result.admitted_extent_bound <= result.padded_extent


def test_temporal_image_construction_does_not_observe_provider_coordinates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    (
        _actions,
        primitive,
        _semantics,
        runtime,
        outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    left = runtime.initial(primitive, 0)
    right = runtime.initial(primitive, 1)
    initial = images.bind_initial(
        producer, binding, producer.compile(binding), left, right
    )

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("temporal construction observed a provider coordinate")

    monkeypatch.setattr(outputs, "observe", forbidden)
    result = images.step(initial, left, right)
    assert images.resolve(result).predecessor == initial


def test_temporal_image_reuses_compressed_blank_subtrees() -> None:
    source = (7, 19, *(19 for _ in range(30)))
    (
        _actions,
        primitive,
        semantics,
        runtime,
        _outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    left = runtime.initial(primitive, 0)
    right = runtime.initial(primitive, 1)
    initial = images.bind_initial(
        producer, binding, producer.compile(binding), left, right
    )
    before = semantics.ledger.counters.get("higher_temporal_image_node_visits", 0)
    images.step(initial, left, right)
    visits = semantics.ledger.counters["higher_temporal_image_node_visits"] - before
    assert visits < 2 * len(source) - 1


def test_temporal_image_workspace_rolls_back_failed_memo_insertion(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    (
        _actions,
        primitive,
        _semantics,
        runtime,
        _outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    left = runtime.initial(primitive, 0)
    right = runtime.initial(primitive, 1)
    initial = images.bind_initial(
        producer, binding, producer.compile(binding), left, right
    )
    original = LedgerDict.__setitem__

    def fail_built(
        store: LedgerDict[object, object], key: object, value: object
    ) -> None:
        if store is images._built:
            raise RuntimeError("injected temporal memo failure")
        original(store, key, value)

    monkeypatch.setattr(LedgerDict, "__setitem__", fail_built)
    with pytest.raises(RuntimeError, match="injected"):
        images.step(initial, left, right)
    assert not images._frames and not images._built
    assert images.ledger._account(images._frame_owner).entries == 0
    assert images.ledger._account(images._built_owner).entries == 0


def test_temporal_image_inventory_and_seal_track_issued_records() -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    (
        _actions,
        primitive,
        _semantics,
        runtime,
        _outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    left = runtime.initial(primitive, 0)
    right = runtime.initial(primitive, 1)
    initial = images.bind_initial(
        producer, binding, producer.compile(binding), left, right
    )
    images.step(initial, left, right)
    assert not audit_higher_payloads(images.ledger).invalid

    record = images._nodes[initial.local_id]
    object.__setattr__(record.macro, "width", True)
    assert audit_higher_payloads(images.ledger).invalid


def test_temporal_image_rejects_replaced_arena_and_source_authority() -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    (
        _actions,
        primitive,
        _semantics,
        runtime,
        _outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    image = images.bind_initial(
        producer,
        binding,
        producer.compile(binding),
        runtime.initial(primitive, 0),
        runtime.initial(primitive, 1),
    )
    owner = images.owner
    images.owner = ArenaToken("substituted-temporal-owner")
    with pytest.raises(ValueError, match="issued authority"):
        images.resolve(image)
    images.owner = owner

    source_owner = images.sources.owner
    images.sources.owner = ArenaToken("substituted-source-owner")
    with pytest.raises(ValueError, match="issued authority"):
        images.resolve(image)
    images.sources.owner = source_owner
    assert images.resolve(image).source == binding


def test_symbolic_macro_constructor_does_not_grant_source_binding() -> None:
    source = (7, 18, 7, 19, 19, 19, 19, 19)
    (
        _actions,
        primitive,
        _semantics,
        runtime,
        _outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    issued = producer.compile(binding)
    fabricated = SourceBoundHigherMacro(
        issued.interface,
        issued.output,
        issued.width,
        issued.source_extent - 1,
        issued.activity,
        issued.first_active,
        issued.last_active,
        issued.extent,
        issued.growth,
    )
    with pytest.raises(ValueError, match="not bound"):
        images.bind_initial(
            producer,
            binding,
            fabricated,
            runtime.initial(primitive, 0),
            runtime.initial(primitive, 1),
        )


@pytest.mark.parametrize(
    "source",
    (
        (7, 18, 7, 19, 19, 19, 19, 19),
        (19, 19, 19, 19, 19, 19, 19, 19),
    ),
)
def test_temporal_image_publishes_complete_split_interface_channels(
    source: tuple[int, ...],
) -> None:
    (
        _actions,
        primitive,
        semantics,
        runtime,
        outputs,
        producer,
        images,
        binding,
    ) = _construction(source)
    left = runtime.initial(primitive, 0)
    right = runtime.initial(primitive, 1)
    initial = images.bind_initial(
        producer, binding, producer.compile(binding), left, right
    )
    prior = images.resolve(initial)
    result = images.resolve(images.step(initial, left, right))
    prior_word = tuple(
        outputs.observe(prior.macro.output, coordinate, 0, 0)
        for coordinate in range(prior.padded_extent)
    )
    expected = _bound_step(prior_word, 0, 0)
    expected_left, expected_right = _bound_exits(prior_word, 0, 0)
    interface = images.interfaces.resolve(result.macro.interface)
    signature = images.interfaces.interface(interface.signature)
    ports = {port.role: port.variable for port in signature.inputs}
    environment = {
        ports["left-boundary"]: 0,
        ports["right-boundary"]: 0,
    }
    components = interface.components
    assert type(components.boundary_left) is HigherExpressionID
    assert type(components.boundary_right) is HigherExpressionID
    assert semantics.evaluate(components.boundary_left, environment) == expected_left
    assert semantics.evaluate(components.boundary_right, environment) == expected_right
    assert components.output == result.macro.output
    assert components.normalization == result.macro.output
    active_positions = [index for index, symbol in enumerate(expected) if symbol != 19]
    active = int(bool(active_positions))
    for role, expected_value in (
        ("activity", active),
        ("first_active", 0),
        ("last_active", 0),
        ("extent", active),
        ("growth", 0),
        ("termination", 1 - active),
        ("halo_left", 0),
        ("halo_right", 0),
        ("frame", 0),
    ):
        component = getattr(components, role)
        assert type(component) is HigherExpressionID
        assert semantics.evaluate(component, environment) == expected_value
    global_environment = environment
    expected_extent = 0 if not active_positions else active_positions[-1] + 1
    assert semantics.evaluate(result.macro.activity, global_environment) == active
    assert (
        semantics.evaluate(result.macro.extent, global_environment) == expected_extent
    )
    encoded_growth = semantics.evaluate(result.macro.growth, global_environment)
    assert type(encoded_growth) is int
    decoded_growth = encoded_growth - result.macro.width
    assert decoded_growth == expected_extent - prior.active_extent


def test_provider_rejects_foreign_binding_before_warm_alias() -> None:
    actions, primitive, semantics, runtime, outputs, producer, _images, binding = (
        _construction((7, 18, 7, 19, 19, 19, 19, 19))
    )
    macro = producer.compile(binding)
    provider = HigherTemporalProviderEvaluator(
        runtime,
        validate_output=outputs.resolve,
        validate_binding=producer.validate_provider_binding,
        compose_actions=actions.compose,
    )
    foreign = producer.sources.forest(1, 4)
    for warm in (False, True):
        if warm:
            provider.bind(macro.output, binding, primitive)
        before = dict(semantics.ledger.counters)
        with pytest.raises(ValueError, match="source was never compiled"):
            provider.bind(macro.output, foreign, primitive)
        with pytest.raises(ValueError, match="another consumer action"):
            provider.bind(macro.output, binding, actions.identity)
        assert dict(semantics.ledger.counters) == before
        assert len(provider._bindings) == int(warm)
    provider.bind(macro.output, binding, primitive)
    assert provider.complete_action(macro.output, primitive) == actions.compose(
        primitive, primitive
    )
    # Issued provenance remains valid when the construction workspace is cleared.
    producer.clear()
    assert provider.complete_action(macro.output, primitive) == actions.compose(
        primitive, primitive
    )


@pytest.mark.parametrize(
    "field", ("_validate_output", "_validate_binding", "_compose_actions", "runtime")
)
def test_provider_rejects_replaced_authority_before_a_warm_lookup(
    field: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    actions, primitive, semantics, runtime, outputs, producer, _images, binding = (
        _construction((7, 18, 7, 19))
    )
    macro = producer.compile(binding)
    provider = HigherTemporalProviderEvaluator(
        runtime,
        validate_output=outputs.resolve,
        validate_binding=producer.validate_provider_binding,
        compose_actions=actions.compose,
    )
    provider.bind(macro.output, binding, primitive)

    def replacement_callback(*args: object) -> None:
        pass

    replacement: object = replacement_callback
    if field == "runtime":
        replacement = _construction((7, 18, 7, 19))[3]
    before = dict(semantics.ledger.counters)
    with monkeypatch.context() as patch:
        patch.setattr(provider, field, replacement)
        with pytest.raises(ValueError, match="issued authority"):
            provider.bind(macro.output, binding, primitive)
        with pytest.raises(ValueError, match="issued authority"):
            provider.complete_action(macro.output, primitive)
        with pytest.raises(ValueError, match="issued authority"):
            provider(macro.output, primitive, macro.interface, 0, 0, 0)
        assert dict(semantics.ledger.counters) == before
    assert provider.complete_action(macro.output, primitive) == actions.compose(
        primitive, primitive
    )


def test_provider_rejects_another_compiled_sources_output() -> None:
    actions, primitive, _semantics, runtime, outputs, producer, _images, binding = (
        _construction((7, 18, 7, 19, 19, 19, 19, 19))
    )
    original = producer.compile(binding)
    foreign = producer.sources.forest(1, 4)
    other = producer.compile(foreign)
    assert other.output != original.output
    provider = HigherTemporalProviderEvaluator(
        runtime,
        validate_output=outputs.resolve,
        validate_binding=producer.validate_provider_binding,
        compose_actions=actions.compose,
    )
    with pytest.raises(ValueError, match="differs from its bound source output"):
        provider.bind(original.output, foreign, primitive)
    assert not provider._bindings
    provider.bind(other.output, foreign, primitive)
    provider.bind(original.output, binding, primitive)
    assert len(provider._bindings) == 2


@pytest.mark.parametrize("target", ("provider", "composer"))
def test_empty_provider_and_composer_audits_check_authority(
    target: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    actions, _primitive, semantics, runtime, outputs, producer, _images, _binding = (
        _construction((7, 18, 7, 19))
    )
    provider = HigherTemporalProviderEvaluator(
        runtime,
        validate_output=outputs.resolve,
        validate_binding=producer.validate_provider_binding,
        compose_actions=actions.compose,
    )
    assert not audit_higher_payloads(semantics.ledger).invalid
    if target == "provider":
        monkeypatch.setattr(provider, "_validate_binding", lambda *args: None)
        expected = provider._binding_owner, id(provider._bindings)
    else:
        monkeypatch.setattr(producer, "blank", 0)
        expected = producer._binding_owner, id(producer._bindings)
    assert expected in audit_higher_payloads(semantics.ledger).invalid
