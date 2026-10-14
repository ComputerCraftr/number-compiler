"""The decimal pair output is published by the source-image scheduler."""

from __future__ import annotations

from collections.abc import Generator, MutableMapping
from dataclasses import replace
from typing import cast

import pytest

from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.reverse_source_payload_audit import (
    audit_reverse_source_payloads,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveTemporalCutover,
)
from number_compiler.sequences.reverse_add.source_images import (
    ReverseImagePayload,
    ReverseSourceImageWorkspace,
)
from tests.support.reference_arithmetic import literal_reverse_add_digits
from tests.support.reverse_cutover import (
    assert_q19_application_counts_unchanged,
    q19_application_counts,
)
from tests.support.source_image_assertions import assert_exact_digit_observers


@pytest.mark.parametrize("seed", (196, 99, 999))
def test_decimal_q19_output_is_the_completed_scheduler_payload(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    steps = 20
    term = ReverseAddPoweredTerm(seed, steps)
    expected = literal_reverse_add_digits(seed, steps)

    def forbidden_legacy_replay(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("decimal output entered the recursive field cutover")

    # The decimal result must come from the scheduler-owned pair occurrence,
    # rather than rebuilding the same endpoint through the recursive evaluator.
    monkeypatch.setattr(
        ReverseRecursiveTemporalCutover,
        "pair_image",
        forbidden_legacy_replay,
    )
    try:
        assert_exact_digit_observers(term, expected)

        workspace = term._workspace
        assert workspace is not None
        image = workspace._image
        assert image is not None
        payload = workspace.scheduler._source_image_core().view(image).payload
        assert isinstance(payload, ReverseImagePayload)
        assert payload.pair_output is not None
        assert payload.pair_output.temporal_steps == steps
        assert payload.pair_output.output_width == len(expected)
        counters = workspace.ledger.counters
        assert counters.get("source_image_primitive_applications", 0) == 0
        assert (
            2 * counters.get("reverse_q19_punctured_t2_applications", 0)
            + 4 * counters.get("reverse_q19_punctured_t4_applications", 0)
            + counters.get("reverse_q19_primitive_pair_applications", 0)
            > 0
        )
        assert counters.get("reverse_q19_punctured_emitted_grammar_nodes", 0) > 0
        assert counters.get("reverse_q19_pair_output_nodes_visited", 0) > 0
    finally:
        workspace = term._workspace
        if workspace is not None:
            workspace.dispose()
            assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_nondecimal_source_keeps_the_existing_image_path() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 41, 2, base=3)
    expected = literal_reverse_add_digits(41, 2, 3)
    assert tuple(workspace.iter_digits()) == expected
    image = workspace._image
    assert image is not None
    payload = workspace.scheduler._source_image_core().view(image).payload
    assert isinstance(payload, ReverseImagePayload)
    assert payload.pair_output is None
    assert workspace.adapter._q19_owner is None
    workspace.dispose()
    assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_width_demand_publishes_completed_q19_output_without_rendering() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
    expected = literal_reverse_add_digits(196, 3)

    assert workspace.width() == len(expected)
    image = workspace._image
    assert image is not None
    owner = workspace.adapter._q19_owner
    assert owner is not None
    payload = workspace.scheduler._source_image_core().view(image).payload
    assert isinstance(payload, ReverseImagePayload)
    assert payload.pair_output is not None
    assert payload.pair_output.output_width == len(expected)
    counters = workspace.ledger.counters
    assert counters.get("reverse_q19_primitive_pair_applications", 0) == 0
    assert counters.get("reverse_successor_tape_width_compilations", 0) == 0
    assert counters.get("recursive_output_stream_emitted_digits", 0) == 0
    assert (
        2 * counters.get("reverse_q19_punctured_t2_applications", 0)
        + 4 * counters.get("reverse_q19_punctured_t4_applications", 0)
        > 0
    )
    assert workspace.completed_width_if_cached() == len(expected)
    assert counters.get("recursive_output_stream_emitted_digits", 0) == 0

    assert tuple(workspace.iter_digits()) == expected
    assert workspace._image is not None
    assert workspace.adapter._q19_owner is not None
    assert workspace.width() == len(expected)
    assert counters.get("reverse_successor_tape_width_compilations", 0) == 0
    assert counters.get("reverse_q19_primitive_pair_applications", 0) == 0
    assert counters.get("recursive_output_stream_emitted_digits", 0) == len(expected)
    workspace.dispose()
    assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_source_image_reset_releases_the_invalidated_q19_owner() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    expected = literal_reverse_add_digits(196, 20)
    assert workspace.width() == len(expected)
    old_owner = workspace.adapter._q19_owner
    assert old_owner is not None
    old_image = workspace._image
    assert old_image is not None
    old_payload = workspace.scheduler._source_image_core().view(old_image).payload
    assert isinstance(old_payload, ReverseImagePayload)
    old_occurrence = old_payload.pair_output
    assert old_occurrence is not None

    workspace.scheduler.clear_source_images()
    assert workspace.width() == len(expected)
    new_owner = workspace.adapter._q19_owner
    assert new_owner is not None and new_owner is not old_owner
    assert old_owner._disposed
    assert len(old_owner.arena.nodes) == 0
    with pytest.raises(ValueError, match="disposed"):
        old_owner.validate(old_occurrence)
    workspace.dispose()
    assert workspace.ledger.entries == workspace.ledger.nodes == 0
    assert workspace.ledger.audit_payload_contracts().invalid == frozenset()


def test_completed_output_first_reuses_its_width_without_reconstruction() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    expected = literal_reverse_add_digits(196, 20)

    assert tuple(workspace.iter_digits()) == expected
    image = workspace._image
    assert image is not None
    owner = workspace.adapter._q19_owner
    assert owner is not None
    t2_applications = workspace.ledger.counters.get(
        "reverse_q19_punctured_t2_applications", 0
    )
    t4_applications = workspace.ledger.counters.get(
        "reverse_q19_punctured_t4_applications", 0
    )
    primitive_applications = workspace.ledger.counters.get(
        "reverse_q19_primitive_pair_applications", 0
    )
    assert 2 * t2_applications + 4 * t4_applications + primitive_applications > 0
    assert workspace.width() == len(expected)
    assert workspace.width() == len(expected)
    assert workspace._image == image
    assert workspace.adapter._q19_owner is owner
    assert (
        workspace.ledger.counters.get("reverse_successor_tape_width_compilations", 0)
        == 0
    )
    assert (
        workspace.ledger.counters.get("reverse_q19_punctured_t2_applications", 0)
        == t2_applications
    )
    assert (
        workspace.ledger.counters.get("reverse_q19_punctured_t4_applications", 0)
        == t4_applications
    )
    assert (
        workspace.ledger.counters.get("reverse_q19_primitive_pair_applications", 0)
        == primitive_applications
    )
    workspace.dispose()


def test_q19_rejects_foreign_occurrence_and_rebound_source() -> None:
    left = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    right = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    try:
        assert left.width() == right.width()
        assert left._image is not None and right._image is not None
        assert tuple(left.iter_digits()) == literal_reverse_add_digits(196, 20)
        assert tuple(right.iter_digits()) == literal_reverse_add_digits(196, 20)
        assert left._image is not None and right._image is not None
        left_view = left.scheduler._source_image_core().view(left._image)
        right_view = right.scheduler._source_image_core().view(right._image)
        left_payload = left_view.payload
        right_payload = right_view.payload
        assert isinstance(left_payload, ReverseImagePayload)
        assert isinstance(right_payload, ReverseImagePayload)
        assert left_payload.pair_output is not None
        assert right_payload.pair_output is not None

        forged_payload = ReverseImagePayload(
            left_payload.action, pair_output=right_payload.pair_output
        )
        with pytest.raises(ValueError):
            left.adapter.validate_payload(forged_payload)

        forged_binding = replace(left_view.binding, source=right.source)
        forged_view = replace(left_view, binding=forged_binding)
        with pytest.raises(ValueError):
            left.adapter.project(forged_view, SourceImageDemand("width"))
    finally:
        left.dispose()
        right.dispose()


@pytest.mark.parametrize("order", ("point-width-stream", "stream-point-width"))
def test_q19_width_point_and_stream_share_one_completed_image(order: str) -> None:
    seed, steps = 196, 20
    expected = literal_reverse_add_digits(seed, steps)
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), seed, steps)
    if order == "point-width-stream":
        assert workspace.digit(0) == expected[0]
        assert workspace.width() == len(expected)
        assert tuple(workspace.iter_digits()) == expected
    else:
        assert tuple(workspace.iter_digits()) == expected
        assert workspace.digit(0) == expected[0]
        assert workspace.width() == len(expected)

    counters = workspace.ledger.counters
    application_counts = q19_application_counts(counters)
    t2_applications, t4_applications, primitive_pairs = application_counts
    assert 2 * t2_applications + 4 * t4_applications + primitive_pairs > 0
    assert counters.get("source_image_primitive_applications", 0) == 0
    assert workspace.width() == len(expected)
    assert_q19_application_counts_unchanged(counters, application_counts)
    workspace.dispose()
    assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_partial_q19_stream_releases_scratch_and_disposes_cleanly() -> None:
    term = ReverseAddPoweredTerm(196, 20)
    stream = term.iter_digits()
    assert isinstance(stream, Generator)
    assert next(stream) == literal_reverse_add_digits(196, 20)[0]
    stream.close()
    workspace = term._workspace
    assert workspace is not None
    assert term._ledger.counters.get("reverse_output_stream_cancellations", 0) == 1
    assert term._ledger.counters.get("recursive_output_stream_emitted_digits", 0) == 1
    scratch = next(
        item
        for item in term._ledger.inventory()
        if item.role == "reverse_pair_output_workspace"
    )
    assert scratch.entries == scratch.nodes == 0
    audit = audit_reverse_source_payloads(
        term._ledger,
        tuple(term._ledger.iter_execution_roots()),
        dict(term._ledger.iter_containers()),
    )
    assert audit.valid(workspace)
    assert not audit.invalid
    workspace.dispose()
    assert term._ledger.entries == term._ledger.nodes == 0


def test_q19_stream_resumed_after_owner_disposal_releases_walk_tasks() -> None:
    term = ReverseAddPoweredTerm(196, 20)
    stream = term.iter_digits()
    next(stream)
    workspace = term._workspace
    assert workspace is not None

    workspace.dispose()
    with pytest.raises(ValueError, match="disposed Q19"):
        next(stream)

    assert term._ledger.entries == term._ledger.nodes == 0


@pytest.mark.parametrize("store_name", ("terminal", "concat", "issued"))
def test_q19_audit_rejects_numeric_alias_keys(store_name: str) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
    try:
        tuple(workspace.iter_digits())
        owner = workspace.adapter._q19_owner
        assert owner is not None
        stores = {
            "terminal": owner.arena._term,
            "concat": owner.arena._cat,
            "issued": owner._issued,
        }
        store = cast(MutableMapping[object, object], stores[store_name])
        key = next(iter(store))
        assert type(key) in (int, tuple)
        alias = (
            float(key)
            if type(key) is int
            else tuple(float(part) for part in cast(tuple[int, ...], key))
        )
        value = store.pop(key)
        store[alias] = value
        audit = workspace.ledger.audit_payload_contracts()
        assert not audit.owns_root("reverse_add", owner, ledger=workspace.ledger)
        store.pop(alias)
        store[key] = value
        repaired = workspace.ledger.audit_payload_contracts()
        assert repaired.owns_root("reverse_add", owner, ledger=workspace.ledger)
    finally:
        workspace.dispose()
