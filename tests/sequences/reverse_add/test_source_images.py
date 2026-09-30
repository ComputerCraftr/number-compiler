"""Focused gates for the bounded reverse/add source-image adapter."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.field_executor import FieldImageCandidate
from number_compiler.hashlife.execution.field_images import SourceCellID
from number_compiler.hashlife.execution.source_bound_images import SourceImageView
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.recursive_adapters import (
    _ReverseRecursiveFieldAdapter,
)
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveTemporalCutover,
)
from number_compiler.sequences.reverse_add.source_images import (
    ReverseActionID,
    ReverseCylinderConstructionUnavailable,
    ReverseImagePayload,
    ReverseSourceImageWorkspace,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from tests.support.reverse_cutover import assert_completed_child_work


def _digits(value: int, base: int) -> tuple[int, ...]:
    result: list[int] = []
    while True:
        result.append(value % base)
        value //= base
        if not value:
            return tuple(result)


def _reverse_add(value: int, steps: int, base: int) -> int:
    for _ in range(steps):
        source = _digits(value, base)
        reverse = sum(
            digit * base**position for position, digit in enumerate(reversed(source))
        )
        value += reverse
    return value


@pytest.mark.parametrize(
    ("seed", "base"), ((0, 10), (196, 10), (999, 10), (11, 2), (41, 3))
)
def test_identity_and_one_primitive_are_exact(seed: int, base: int) -> None:
    source = _digits(seed, base)
    reverse = sum(value * base**position for position, value in enumerate(source[::-1]))
    for steps, expected in ((0, seed), (1, seed + reverse)):
        workspace = ReverseSourceImageWorkspace(
            ResourceLedger(), seed, steps, base=base
        )
        digits = tuple(workspace.iter_digits())
        assert digits == _digits(expected, base)
        assert workspace.width() == len(digits)
        assert tuple(workspace.digit(i) for i in range(len(digits))) == digits


def test_one_step_stream_is_linear_and_retains_no_endpoint_word() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    before = workspace.ledger.counters.get("reverse_source_carry_coordinates", 0)
    assert tuple(workspace.iter_digits()) == (7, 8, 8)
    work = workspace.ledger.counters["reverse_source_carry_coordinates"] - before
    assert work == 3
    image = workspace._image
    assert image is not None
    payload = workspace.scheduler._source_image_core().view(image).payload
    assert not hasattr(payload, "digits")


@pytest.mark.parametrize("seed", (1, 196, int("4" * 128 + "5" * 128)))
def test_one_step_stream_needs_no_random_access_carry_prefix(seed: int) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 1)
    expected = _digits(_reverse_add(seed, 1, 10), 10)
    assert tuple(workspace.iter_digits()) == expected
    assert (
        workspace.ledger.counters.get("reverse_source_ports_layer_1_carry_queries", 0)
        == 0
    )


@pytest.mark.parametrize(
    ("seed", "base"), ((0, 10), (5, 10), (11, 10), (196, 10), (99, 10), (41, 3))
)
def test_fused_second_step_matches_reference_without_midpoint(
    seed: int, base: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2, base=base)
    adapter_type = type(workspace.adapter)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("two-step pullback entered a one-step evaluator")

    monkeypatch.setattr(adapter_type, "apply_primitive", forbidden)
    monkeypatch.setattr(adapter_type, "iter_primitive_digits", forbidden)
    monkeypatch.setattr(adapter_type, "_carry_and_digit", forbidden, raising=False)
    monkeypatch.setattr(adapter_type, "_width", forbidden)
    expected = _digits(_reverse_add(seed, 2, base), base)
    assert tuple(workspace.iter_digits()) == expected
    assert workspace.width() == len(expected)
    assert tuple(workspace.digit(i) for i in range(len(expected))) == expected
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0
    assert (
        workspace.ledger.counters["reverse_source_two_step_pullback_publications"] == 1
    )


@pytest.mark.parametrize(
    "seed",
    (
        int("4" * 512 + "5" * 512),
        int("9" + "4" * 511 + "5" * 511 + "9"),
    ),
)
def test_fused_second_step_full_output_has_linear_source_work(seed: int) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2)
    assert tuple(workspace.iter_digits()) == _digits(_reverse_add(seed, 2, 10), 10)
    width = len(_digits(seed, 10))
    assert workspace.ledger.counters["reverse_source_pullback_pair_reads"] <= 8 * width


@pytest.mark.parametrize("seed", (0, 1, 18, 196, 909))
def test_second_step_stream_uses_one_physical_carry_without_prefix_queries(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2)
    expected = _digits(_reverse_add(seed, 2, 10), 10)
    assert workspace.width() == len(expected)
    before = workspace.ledger.counters.get(
        "reverse_source_ports_layer_2_carry_queries", 0
    )

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("D2 stream repeated a random-access carry or pair query")

    monkeypatch.setattr(SourceCarryPorts, "second_carry", forbidden)
    monkeypatch.setattr(SourceCarryPorts, "second_pair", forbidden)
    monkeypatch.setattr(type(workspace.adapter), "second_digit", forbidden)
    assert tuple(workspace.iter_digits()) == expected
    assert (
        workspace.ledger.counters.get("reverse_source_ports_layer_2_carry_queries", 0)
        == before
    )


@pytest.mark.parametrize(
    "seed",
    (int("4" * 128 + "5" * 128), int("9" + "4" * 127 + "5" * 127 + "9")),
)
def test_large_second_step_stream_eliminates_random_access_prefix_work(
    seed: int,
) -> None:
    expected = _digits(_reverse_add(seed, 2, 10), 10)
    streamed = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2)
    assert tuple(streamed.iter_digits()) == expected
    stream_second_queries = streamed.ledger.counters.get(
        "reverse_source_ports_layer_2_carry_queries", 0
    )
    assert stream_second_queries == 0
    assert (
        streamed.ledger.counters.get("reverse_source_ports_layer_1_carry_queries", 0)
        > 0
    )

    points = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2)
    width = points.width()
    assert width == len(expected)
    assert tuple(points.digit(i) for i in range(width)) == expected
    assert (
        points.ledger.counters.get("reverse_source_ports_layer_2_carry_queries", 0)
        > stream_second_queries
    )


def test_undemanded_second_step_publishes_one_fused_image() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 2)
    image = workspace.scheduler.source_image(
        workspace.adapter, workspace.source, workspace.root_action
    )
    payload = workspace.scheduler._source_image_core().view(image).payload
    assert isinstance(payload, ReverseImagePayload)
    assert workspace.actions.node(payload.action).steps == 2
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0


def test_count_only_d2_image_cannot_authorize_a_right_half() -> None:
    """A returned D2 occurrence needs complete outputs before D4 admission."""
    workspace, view = _two_step_view()
    assert isinstance(view.payload, ReverseImagePayload)
    assert workspace.actions.node(view.payload.action).steps == 2
    with pytest.raises(ReverseCylinderConstructionUnavailable, match="source cylinder"):
        workspace.adapter.admitted_input_key(workspace.root_action, view)

    # Matching numeric action duration and seed do not transfer authority from
    # another occurrence arena. The right-half constructor must check both.
    _unused_foreign_binding, other_view = _two_step_view()
    with pytest.raises(ValueError, match="different arena"):
        workspace.adapter.validate_payload(other_view.payload)


@pytest.mark.parametrize(
    ("seed", "steps", "expected"),
    ((1, 3, 8), (10, 4, 88), (11, 3, 88), (1001, 3, 8008)),
)
def test_powered_same_carry_chamber_is_exact(
    seed: int, steps: int, expected: int
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, steps)
    digits = _digits(expected, 10)
    assert workspace.width() == len(digits)
    assert tuple(workspace.iter_digits()) == digits
    assert tuple(workspace.digit(i) for i in range(len(digits))) == digits
    assert workspace.ledger.counters["reverse_source_same_carry_publications"] == 1
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0


@pytest.mark.parametrize(
    ("seed", "steps", "expected"),
    (
        (1, 4, (6, 1)),
        (196, 3, (6, 3, 4, 7)),
        (111589511, 3, (8, 9, 7, 0, 0, 1, 7, 9, 8)),
    ),
)
def test_rejected_same_carry_uses_completed_child_recursive_occurrence(
    seed: int, steps: int, expected: tuple[int, ...]
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, steps)
    assert tuple(workspace.iter_digits()) == expected
    assert workspace.width() == len(expected)
    assert tuple(workspace.digit(i) for i in range(len(expected))) == expected
    counters = workspace.ledger.counters
    assert_completed_child_work(counters)
    assert counters["reverse_source_chamber_rejections"] >= 1
    assert counters.get("reverse_source_completed_child_publications", 0) == 1
    assert workspace._image is not None


def test_completed_child_parent_join_never_recompiles_nonleaf_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_compile = _ReverseRecursiveFieldAdapter._compile

    def leaf_only_compile(
        self: _ReverseRecursiveFieldAdapter,
        action: FieldCellActionID,
        source: SourceCellID,
    ) -> FieldImageCandidate:
        if self.sources.resolve(source).level > 0:
            raise AssertionError("completed parent was recompiled from source")
        return original_compile(self, action, source)

    def forbidden_terminal_image(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("direct output rebuilt a terminal field image")

    monkeypatch.setattr(_ReverseRecursiveFieldAdapter, "_compile", leaf_only_compile)
    monkeypatch.setattr(
        ReverseRecursiveTemporalCutover, "digit_image", forbidden_terminal_image
    )
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    expected = _digits(_reverse_add(196, 20, 10), 10)
    assert workspace.width() == len(expected)
    assert tuple(workspace.iter_digits()) == expected
    assert workspace.digit(0) == expected[0]
    counters = workspace.ledger.counters
    assert_completed_child_work(counters)


def test_direct_pair_image_uses_joined_children_and_checks_occurrence_authority(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    cutover = ReverseRecursiveTemporalCutover(
        ledger, _digits(196, 10), base=10, maximum_steps=3
    )
    original_compile = _ReverseRecursiveFieldAdapter._compile

    def leaf_only_compile(
        self: _ReverseRecursiveFieldAdapter,
        action: FieldCellActionID,
        source: SourceCellID,
    ) -> FieldImageCandidate:
        if self.sources.resolve(source).level > 0:
            raise AssertionError("direct pair image recompiled a nonleaf source")
        return original_compile(self, action, source)

    monkeypatch.setattr(_ReverseRecursiveFieldAdapter, "_compile", leaf_only_compile)
    occurrence = cutover.pair_image(3)
    assert occurrence.temporal_steps == 3
    assert tuple(cutover.iter_digits(occurrence)) == (6, 3, 4, 7)
    assert ledger.counters.get("reverse_recursive_completed_child_joins", 0) > 0

    wrong_action = replace(occurrence, action=cutover.pair_action(2))
    with pytest.raises(ValueError, match="authority/source/action|duration"):
        cutover.validate_occurrence(wrong_action)
    foreign = ReverseRecursiveTemporalCutover(
        ResourceLedger(), _digits(89, 10), base=10, maximum_steps=3
    )
    wrong_source = replace(occurrence, source=foreign.source)
    with pytest.raises(ValueError, match="authority/source/action"):
        cutover.validate_occurrence(wrong_source)


def test_terminal_digit_does_not_replay_prefix_and_partial_stream_is_charged() -> None:
    cutover = ReverseRecursiveTemporalCutover(
        ResourceLedger(), _digits(196, 10), base=10, maximum_steps=3
    )
    occurrence = cutover.pair_image(3)
    descent_key = "reverse_recursive_pair_width_descents"
    before_descents = cutover.ledger.counters.get(descent_key, 0)
    pair_width = cutover.pair_width(occurrence)
    one_width = cutover.ledger.counters[descent_key] - before_descents
    before_descents = cutover.ledger.counters[descent_key]
    before = cutover.ledger.counters.get("reverse_recursive_direct_carry_steps", 0)
    try:
        cutover.digit(occurrence, pair_width)
    except IndexError:
        pass
    assert (
        cutover.ledger.counters.get("reverse_recursive_direct_carry_steps", 0) - before
        == pair_width
    )

    assert cutover.ledger.counters[descent_key] - before_descents == one_width

    before_digits = cutover.ledger.counters.get("reverse_recursive_streamed_digits", 0)
    stream = cutover.iter_digits(occurrence)
    next(stream)
    stream.close()
    assert (
        cutover.ledger.counters.get("reverse_recursive_streamed_digits", 0)
        - before_digits
        == 1
    )
    for demand in (
        lambda: cutover.width(occurrence),
        lambda: tuple(cutover.iter_digits(occurrence)),
    ):
        before_descents = cutover.ledger.counters[descent_key]
        demand()
        assert cutover.ledger.counters[descent_key] - before_descents == one_width


def test_zero_source_admits_huge_power_without_constructing_the_power() -> None:
    steps = 10**26
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 0, steps)
    assert workspace.width() == 1
    assert tuple(workspace.iter_digits()) == (0,)
    assert workspace.digit(0) == 0
    assert workspace.operator_nodes <= 2 * steps.bit_length()
    assert workspace.ledger.counters["reverse_source_chamber_admissions"] >= 1


@pytest.mark.parametrize("base", [2, 3, 10])
def test_two_step_small_sources_against_independent_arithmetic(base: int) -> None:
    for seed in range(512):
        workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2, base=base)
        assert tuple(workspace.iter_digits()) == _digits(
            _reverse_add(seed, 2, base), base
        )
        workspace.dispose()
        assert workspace.ledger.nodes == workspace.ledger.entries == 0


def test_composite_demand_uses_completed_children_without_primitive_descent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    adapter_type = type(workspace.adapter)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("composite demand descended to a source-image primitive")

    monkeypatch.setattr(adapter_type, "apply_primitive", forbidden)
    assert workspace.width() == 11
    assert workspace.digit(0) == 6
    counters = workspace.ledger.counters
    assert_completed_child_work(counters)


def test_undemanded_scheduler_entry_publishes_completed_child_image_without_primitive(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 8)
    adapter_type = type(workspace.adapter)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("undemanded image descended to a source-image primitive")

    monkeypatch.setattr(adapter_type, "apply_primitive", forbidden)
    first = workspace.scheduler.source_image(
        workspace.adapter, workspace.source, workspace.root_action
    )
    second = workspace.scheduler.source_image(
        workspace.adapter, workspace.source, workspace.root_action
    )
    assert first == second
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0
    assert (
        workspace.ledger.counters.get("reverse_recursive_completed_child_joins", 0) > 0
    )


def test_descriptor_is_lazy_logarithmic_and_handles_are_scoped() -> None:
    left = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1 << 40)
    right = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    assert left.operator_nodes <= 42
    assert left.compose_operations <= 40
    assert left.syntax_depth_bound <= 41
    foreign = ReverseActionID(
        right.root_action.owner,
        right.root_action.kind,
        right.root_action.local_id,
    )
    with pytest.raises(ValueError, match="different arena"):
        left.actions.node(foreign)
    left.dispose()
    with pytest.raises(ValueError, match="disposed"):
        left.actions.node(left.root_action)


def test_dispose_releases_retained_images_and_actions() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    assert workspace.digit(0) == 7
    workspace.dispose()
    assert workspace.ledger.entries == 0
    assert workspace.ledger.nodes == 0
    with pytest.raises(ValueError, match="disposed"):
        workspace.width()


def test_workspace_rejects_mutated_public_bindings() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    workspace.steps = 0
    with pytest.raises(ValueError, match="binding was altered"):
        workspace.digit(0)
    workspace.dispose()

    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    foreign = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    workspace.source = foreign.source
    with pytest.raises(ValueError, match="binding was altered"):
        workspace.width()
    workspace.dispose()
    foreign.dispose()


@pytest.mark.parametrize(
    "ledger", (ResourceLedger(max_nodes=1), ResourceLedger(max_cache_entries=5))
)
def test_failed_workspace_construction_releases_every_reservation(
    ledger: ResourceLedger,
) -> None:
    with pytest.raises(RuntimeError):
        ReverseSourceImageWorkspace(ledger, 196, 1)
    assert ledger.entries == 0
    assert ledger.nodes == 0


def _two_step_view() -> tuple[ReverseSourceImageWorkspace, SourceImageView]:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 2)
    image = workspace.scheduler.source_image(
        workspace.adapter, workspace.source, workspace.root_action
    )
    view = workspace.scheduler._source_image_core().view(image)
    return workspace, view


def test_disposed_recursive_constructor_refuses_before_allocating() -> None:
    cutover = ReverseRecursiveTemporalCutover(
        ResourceLedger(), (6, 9, 1), base=10, maximum_steps=8
    )
    cutover.pair_image(3)
    before = cutover.ledger.snapshot()
    with pytest.raises(ValueError, match="horizon"):
        cutover.pair_action(9)
    assert cutover.ledger.snapshot() == before
    cutover.dispose()
    before = cutover.ledger.snapshot()
    for constructor in (cutover.pair_action, cutover.pair_image):
        with pytest.raises(ValueError, match="disposed"):
            constructor(8)
        assert cutover.ledger.snapshot() == before
