"""Focused gates for the bounded reverse/add source-image adapter."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Sized
from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.hashlife.actions.field_actions import (
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.field_executor import FieldImageCandidate
from number_compiler.hashlife.execution.field_images import SourceCellID
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.recursive_adapters import (
    ReverseRecursiveFieldAdapter,
)
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveTemporalCutover,
)
from number_compiler.sequences.reverse_add.source_images import (
    ReverseActionID,
    ReverseImagePayload,
    ReverseSourceImageWorkspace,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from tests.support.payload_audit_failures import (
    assert_payload_publication_released,
    fail_after_payload_audit_publication,
)
from tests.support.reference_arithmetic import literal_reverse_add_digits
from tests.support.reverse_cutover import assert_completed_child_work
from tests.support.source_image_assertions import assert_exact_digit_observers


@pytest.mark.parametrize(
    ("seed", "base"), ((0, 10), (196, 10), (999, 10), (11, 2), (41, 3))
)
def test_identity_and_one_primitive_are_exact(seed: int, base: int) -> None:
    for steps in (0, 1):
        workspace = ReverseSourceImageWorkspace(
            ResourceLedger(), seed, steps, base=base
        )
        digits = tuple(workspace.iter_digits())
        assert digits == literal_reverse_add_digits(seed, steps, base)
        assert workspace.width() == len(digits)
        assert tuple(workspace.digit(i) for i in range(len(digits))) == digits


def test_one_step_stream_is_linear_and_retains_no_endpoint_word() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 1)
    assert tuple(workspace.iter_digits()) == (7, 8, 8)
    counters = workspace.ledger.counters
    assert counters.get("reverse_q19_primitive_pair_applications", 0) == 0
    assert counters["recursive_output_stream_emitted_digits"] == 3
    image = workspace._image
    assert image is not None
    payload = workspace.scheduler._source_image_core().view(image).payload
    assert not hasattr(payload, "digits")
    assert isinstance(payload, ReverseImagePayload)
    assert payload.pair_output is not None
    assert payload.pair_output.temporal_steps == 1
    assert workspace.adapter._q19_source is workspace.actions.source(workspace.source)


@pytest.mark.parametrize("seed", (1, 196, int("4" * 128 + "5" * 128)))
def test_one_step_stream_needs_no_random_access_carry_prefix(seed: int) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 1)
    expected = literal_reverse_add_digits(seed, 1)
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
    expected = literal_reverse_add_digits(seed, 2, base)
    assert_exact_digit_observers(workspace, expected)
    assert workspace.ledger.counters.get("source_image_primitive_applications", 0) == 0
    if base == 10:
        assert workspace.ledger.counters["reverse_q19_root_bootstrap_publications"] == 1
        assert workspace.ledger.counters["reverse_q19_root_bootstrap_pair_steps"] == 1
        assert workspace.ledger.counters["reverse_q19_primitive_pair_applications"] == 1
    else:
        assert (
            workspace.ledger.counters["reverse_source_two_step_pullback_publications"]
            == 1
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
    expected = literal_reverse_add_digits(seed, 2)
    assert tuple(workspace.iter_digits()) == expected
    width = len(literal_reverse_add_digits(seed, 0))
    counters = workspace.ledger.counters
    assert 0 < counters["reverse_q19_pair_output_nodes_visited"] <= 16 * width
    assert counters["recursive_output_stream_node_visits"] <= 8 * len(expected)
    assert counters["recursive_output_stream_emitted_digits"] == len(expected)


@pytest.mark.parametrize("seed", (0, 1, 18, 196, 909))
def test_second_step_stream_uses_one_physical_carry_without_prefix_queries(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2)
    expected = literal_reverse_add_digits(seed, 2)
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
    expected = literal_reverse_add_digits(seed, 2)
    streamed = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2)
    assert tuple(streamed.iter_digits()) == expected
    stream_second_queries = streamed.ledger.counters.get(
        "reverse_source_ports_layer_2_carry_queries", 0
    )
    assert stream_second_queries == 0
    assert (
        streamed.ledger.counters.get("reverse_source_ports_layer_1_carry_queries", 0)
        == 0
    )
    assert streamed.ledger.counters["recursive_output_stream_node_visits"] > 0
    assert streamed.ledger.counters["recursive_output_stream_node_visits"] <= 8 * len(
        expected
    )

    points = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2)
    width = points.width()
    assert width == len(expected)
    assert tuple(points.digit(i) for i in range(width)) == expected
    assert (
        points.ledger.counters.get("reverse_source_ports_layer_2_carry_queries", 0) == 0
    )
    assert points.ledger.counters["reverse_q19_point_region_visits"] > 0


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
    """A forged duration-only D2 payload cannot impersonate Q19 output."""
    workspace, view = _two_step_view()
    assert isinstance(view.payload, ReverseImagePayload)
    assert workspace.actions.node(view.payload.action).steps == 2
    incomplete_payload = replace(view.payload, pair_output=None)
    origin = workspace.actions.source(workspace.source)
    incomplete_binding = replace(
        view.binding,
        boundary_ports=(0, 1),
        precision=len(origin.digits) + 2,
    )
    incomplete_view = replace(
        view, binding=incomplete_binding, payload=incomplete_payload
    )
    with pytest.raises(ValueError, match="incomplete Q19 output payload"):
        workspace.adapter.admitted_input_key(workspace.root_action, incomplete_view)

    # Matching numeric action duration and seed do not transfer authority from
    # another occurrence arena. The right-half constructor must check both.
    _unused_foreign_binding, other_view = _two_step_view()
    with pytest.raises(ValueError, match="different arena"):
        workspace.adapter.validate_payload(other_view.payload)


@pytest.mark.parametrize(
    ("seed", "steps", "expected"),
    ((1, 3, (8,)), (10, 4, (8, 8)), (11, 3, (8, 8)), (1001, 3, (8, 0, 0, 8))),
)
def test_q19_completed_output_is_exact_for_small_decimal_words(
    seed: int, steps: int, expected: tuple[int, ...]
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, steps)
    assert workspace.width() == len(expected)
    assert tuple(workspace.iter_digits()) == expected
    assert tuple(workspace.digit(i) for i in range(len(expected))) == expected
    counters = workspace.ledger.counters
    assert counters["reverse_q19_root_bootstrap_publications"] == 1
    assert counters["reverse_q19_root_bootstrap_pair_steps"] == steps - 1
    assert counters.get("source_image_primitive_applications", 0) == 0
    assert workspace._image is not None
    view = workspace.scheduler._source_image_core().view(workspace._image)
    assert isinstance(view.payload, ReverseImagePayload)
    assert view.payload.pair_output is not None
    assert workspace.adapter._q19_owner is not None
    workspace.adapter._q19_owner.validate(view.payload.pair_output)
    assert view.payload.pair_output.temporal_steps == steps


@pytest.mark.parametrize(
    ("seed", "steps", "expected"),
    (
        (1, 4, (6, 1)),
        (196, 3, (6, 3, 4, 7)),
        (111589511, 3, (8, 9, 7, 0, 0, 1, 7, 9, 8)),
    ),
)
def test_small_decimal_composite_uses_authenticated_q19_occurrence(
    seed: int, steps: int, expected: tuple[int, ...]
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, steps)
    assert tuple(workspace.iter_digits()) == expected
    assert workspace.width() == len(expected)
    assert tuple(workspace.digit(i) for i in range(len(expected))) == expected
    counters = workspace.ledger.counters
    assert_completed_child_work(counters)
    assert counters["reverse_q19_root_bootstrap_publications"] == 1
    assert counters["reverse_q19_root_bootstrap_pair_steps"] == steps - 1
    assert workspace._image is not None
    payload = workspace.scheduler._source_image_core().view(workspace._image).payload
    assert isinstance(payload, ReverseImagePayload)
    assert payload.pair_output is not None
    assert workspace.adapter._q19_owner is not None
    workspace.adapter._q19_owner.validate(payload.pair_output)
    assert payload.pair_output.temporal_steps == steps


def test_completed_child_parent_join_never_recompiles_nonleaf_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_leaf = ReverseRecursiveFieldAdapter.leaf

    def checked_leaf(
        self: ReverseRecursiveFieldAdapter,
        action: FieldCellActionID,
        source: SourceCellID,
        geometry: FieldGeometryID,
    ) -> FieldImageCandidate:
        if self.sources.resolve(source).level > 0:
            raise AssertionError("completed parent was recompiled from source")
        return original_leaf(self, action, source, geometry)

    def forbidden_terminal_image(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("direct output rebuilt a terminal field image")

    monkeypatch.setattr(ReverseRecursiveFieldAdapter, "leaf", checked_leaf)
    monkeypatch.setattr(
        ReverseRecursiveTemporalCutover, "digit_image", forbidden_terminal_image
    )
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    expected = literal_reverse_add_digits(196, 20)
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
        ledger, literal_reverse_add_digits(196, 0), base=10, maximum_steps=3
    )
    original_leaf = ReverseRecursiveFieldAdapter.leaf

    def checked_leaf(
        self: ReverseRecursiveFieldAdapter,
        action: FieldCellActionID,
        source: SourceCellID,
        geometry: FieldGeometryID,
    ) -> FieldImageCandidate:
        if self.sources.resolve(source).level > 0:
            raise AssertionError("direct pair image recompiled a nonleaf source")
        return original_leaf(self, action, source, geometry)

    monkeypatch.setattr(ReverseRecursiveFieldAdapter, "leaf", checked_leaf)
    occurrence = cutover.pair_image(3)
    assert occurrence.temporal_steps == 3
    assert tuple(cutover.iter_digits(occurrence)) == (6, 3, 4, 7)
    assert ledger.counters.get("reverse_recursive_completed_child_joins", 0) > 0

    wrong_action = replace(occurrence, action=cutover.pair_action(2))
    with pytest.raises(ValueError, match="authority/source/action|duration"):
        cutover.validate_occurrence(wrong_action)
    foreign = ReverseRecursiveTemporalCutover(
        ResourceLedger(), literal_reverse_add_digits(89, 0), base=10, maximum_steps=3
    )
    wrong_source = replace(occurrence, source=foreign.source)
    with pytest.raises(ValueError, match="authority/source/action"):
        cutover.validate_occurrence(wrong_source)


def test_terminal_digit_does_not_replay_prefix_and_partial_stream_is_charged() -> None:
    cutover = ReverseRecursiveTemporalCutover(
        ResourceLedger(), literal_reverse_add_digits(196, 0), base=10, maximum_steps=3
    )
    occurrence = cutover.pair_image(3)
    descent_key = "reverse_recursive_pair_width_descents"
    before_descents = cutover.ledger.counters.get(descent_key, 0)
    pair_width = cutover.pair_width(occurrence)
    assert cutover.ledger.counters[descent_key] > before_descents
    before_descents = cutover.ledger.counters[descent_key]
    key = "reverse_recursive_terminal_reset_prefix_symbols"
    before = cutover.ledger.counters.get(key, 0)
    # The first pair coefficient is decisive; symmetry gives terminal carry
    # without the previous mandatory whole-word carry fold.
    with pytest.raises(IndexError):
        cutover.digit(occurrence, pair_width)
    assert cutover.ledger.counters[key] - before == 1

    assert cutover.ledger.counters[descent_key] == before_descents

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
        assert cutover.ledger.counters[descent_key] == before_descents


def test_zero_source_admits_huge_power_without_constructing_the_power() -> None:
    steps = 10**26
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 0, steps)
    assert workspace.width() == 1
    assert tuple(workspace.iter_digits()) == (0,)
    assert workspace.digit(0) == 0
    assert workspace.operator_nodes <= 2 * steps.bit_length()
    assert (
        workspace.ledger.counters.get("reverse_successor_tape_width_compilations", 0)
        == 0
    )
    assert workspace.adapter._q19_owner is None
    assert workspace._image is None


@pytest.mark.parametrize("fail_after_registration", (False, True))
def test_workspace_constructor_rolls_back_audit_registration(
    fail_after_registration: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    original = ReverseSourceImageWorkspace._register_source_payload_audit_contract

    def fail_registration(self: ReverseSourceImageWorkspace) -> None:
        if fail_after_registration:
            original(self)
        raise RuntimeError("injected source payload registration failure")

    monkeypatch.setattr(
        ReverseSourceImageWorkspace,
        "_register_source_payload_audit_contract",
        fail_registration,
    )
    ledger = ResourceLedger()
    with pytest.raises(RuntimeError, match="injected source payload"):
        ReverseSourceImageWorkspace(ledger, 196, 8)
    assert not any(
        family == "reverse_add" for _root, family in ledger._payload_audit_contracts
    )
    assert ledger.entries == ledger.nodes == 0


def test_workspace_constructor_removes_contract_if_ledger_register_then_raises(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    published_roots = fail_after_payload_audit_publication(
        monkeypatch, RuntimeError("injected failure after ledger publication")
    )
    with pytest.raises(RuntimeError, match="after ledger publication"):
        ReverseSourceImageWorkspace(ledger, 196, 8)

    assert len(published_roots) == 1
    root = published_roots[0]
    assert_payload_publication_released(ledger, root, "reverse_add")


def test_adapter_memo_construction_failure_retires_its_registered_owner(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_register = ResourceLedger.register_container
    failed_once = False

    def register_then_fail(
        ledger: ResourceLedger,
        owner: int,
        container: Sized,
        *,
        node_count: Callable[[], int] | None = None,
        payloads: Callable[[], Iterable[object]] | None = None,
        roots: Callable[[], Iterable[ArenaHandle]] | None = None,
        evict: Callable[[], None] | None = None,
        composition_count: Callable[[], int] | None = None,
    ) -> None:
        nonlocal failed_once
        original_register(
            ledger,
            owner,
            container,
            node_count=node_count,
            payloads=payloads,
            roots=roots,
            evict=evict,
            composition_count=composition_count,
        )
        if (
            not failed_once
            and ledger._account(owner).role == "reverse_recursive_occurrence_binding"
        ):
            failed_once = True
            raise RuntimeError("injected recursive occurrence memo failure")

    monkeypatch.setattr(ResourceLedger, "register_container", register_then_fail)
    ledger = ResourceLedger()
    with pytest.raises(RuntimeError, match="recursive occurrence memo failure"):
        ReverseSourceImageWorkspace(ledger, 196, 8)
    assert failed_once
    assert all(
        account.disposed and account.entries == account.nodes == 0
        for account in ledger.inventory()
    )

    workspace = ReverseSourceImageWorkspace(ledger, 196, 8)
    try:
        assert workspace.width() == len(literal_reverse_add_digits(196, 8, 10))
    finally:
        workspace.dispose()


@pytest.mark.parametrize("base", [2, 3, 10])
@pytest.mark.parametrize(
    "exhaustive", [False, pytest.param(True, marks=pytest.mark.validation)]
)
def test_two_step_small_sources_against_independent_arithmetic(
    base: int, exhaustive: bool
) -> None:
    seeds = (
        range(512)
        if exhaustive
        else (0, 1, base - 1, base, base + 1, base**2 - 1, base**2, 196, 511)
    )
    for seed in seeds:
        workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, 2, base=base)
        assert tuple(workspace.iter_digits()) == literal_reverse_add_digits(
            seed, 2, base
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


def test_width_demand_admits_completed_q19_image_without_rendering_digits() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    assert workspace.width() == 11
    counters = workspace.ledger.counters
    # The Q19 constructor may consume bounded primitive pair leaves inside its
    # completed grammar. The scheduler must not fall back to the generic
    # source-image primitive path for this composite request.
    assert counters.get("source_image_primitive_applications", 0) == 0
    image = workspace._image
    assert image is not None
    assert workspace.adapter._q19_owner is not None
    payload = workspace.scheduler._source_image_core().view(image).payload
    assert isinstance(payload, ReverseImagePayload)
    assert payload.pair_output is not None
    assert payload.pair_output.output_width == 11
    assert counters.get("reverse_successor_tape_width_compilations", 0) == 0
    assert counters.get("recursive_output_stream_emitted_digits", 0) == 0
    workspace.dispose()


def test_reset_in_another_workspace_does_not_invalidate_local_q19_owner() -> None:
    ledger = ResourceLedger()
    first = ReverseSourceImageWorkspace(ledger, 196, 3)
    second = ReverseSourceImageWorkspace(ledger, 295, 3)
    try:
        expected_width = second.width()
        image = second._image
        q19_owner = second.adapter._q19_owner
        assert image is not None
        assert q19_owner is not None
        second_cache_owner = second.scheduler._source_image_core().owner
        clears_before = ledger.counters.get("source_image_cache_clears", 0)

        first.scheduler.clear_source_images()

        assert ledger.counters["source_image_cache_clears"] == clears_before + 1
        second._check_open()
        assert second.scheduler._source_image_core().owner is second_cache_owner
        assert second._image is image
        assert second.adapter._q19_owner is q19_owner
        assert not q19_owner._disposed
        assert second.width() == expected_width
    finally:
        first.dispose()
        second.dispose()


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
        workspace.ledger.counters.get("reverse_source_completed_chronological_joins", 0)
        > 0
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
