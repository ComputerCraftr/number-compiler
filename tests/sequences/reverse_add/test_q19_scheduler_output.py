"""The decimal pair output is published by the source-image scheduler."""

from __future__ import annotations

from collections.abc import Callable, Generator, MutableMapping, Sequence
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
        assert counters.get("source_image_primitive_applications", 0) >= steps
        assert counters.get("reverse_q19_primitive_pair_applications", 0) >= steps - 1
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


def test_successor_width_stays_scalar_until_the_output_is_requested() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
    expected = literal_reverse_add_digits(196, 3)

    assert workspace.width() == len(expected)
    assert workspace._image is None
    assert workspace.adapter._q19_owner is None
    counters = workspace.ledger.counters
    assert counters["reverse_successor_tape_width_compilations"] == 1
    assert counters["reverse_successor_tape_rows"] == 3
    assert counters["reverse_successor_tape_bootstrap_rows"] == 3
    assert counters.get("reverse_q19_primitive_pair_applications", 0) == 0
    assert workspace.completed_width_if_cached() == len(expected)
    assert counters["reverse_successor_tape_width_compilations"] == 1

    assert tuple(workspace.iter_digits()) == expected
    assert workspace._image is not None
    assert workspace.adapter._q19_owner is not None
    assert workspace.width() == len(expected)
    assert counters["reverse_successor_tape_width_compilations"] == 1
    assert counters.get("reverse_q19_primitive_pair_applications", 0) >= 2
    workspace.dispose()
    assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_successor_width_uses_live_carry_suffix_after_bootstrap(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry.event_memory import (
        _pair_step_with_carry,
        event_memory_horizon,
    )
    from number_compiler.sequences.reverse_add import successor_width

    horizon = event_memory_horizon(10)
    original_step = _pair_step_with_carry
    bootstrap_calls = 0

    def bootstrap_only(
        source: Sequence[int], base: int, *, incoming: int = 0
    ) -> tuple[tuple[int, ...], int, tuple[int, ...]]:
        nonlocal bootstrap_calls
        if bootstrap_calls >= horizon:
            raise AssertionError("live successor tape replayed a pair transition")
        bootstrap_calls += 1
        return original_step(source, base, incoming=incoming)

    monkeypatch.setattr(successor_width, "_pair_step_with_carry", bootstrap_only)
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 256)
    expected = literal_reverse_add_digits(196, 256)
    assert workspace.width() == len(expected)
    assert bootstrap_calls == horizon
    counters = workspace.ledger.counters
    assert counters["reverse_successor_tape_rows"] == 256
    assert counters["reverse_successor_tape_bootstrap_rows"] == horizon
    assert counters["reverse_successor_tape_spatial_bits"] > 0
    assert counters["reverse_successor_tape_pair_operand_symbols"] > 0
    assert counters["reverse_successor_tape_event_symbols"] > 0
    assert workspace._image is None
    assert workspace.adapter._q19_owner is None
    workspace.dispose()
    assert workspace.ledger.nodes == workspace.ledger.entries == 0


def test_completed_output_first_reuses_its_width_without_successor_work() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    expected = literal_reverse_add_digits(196, 20)

    assert tuple(workspace.iter_digits()) == expected
    image = workspace._image
    assert image is not None
    owner = workspace.adapter._q19_owner
    assert owner is not None
    pair_applications = workspace.ledger.counters.get(
        "reverse_q19_primitive_pair_applications", 0
    )
    assert pair_applications >= 19
    assert workspace.width() == len(expected)
    assert workspace.width() == len(expected)
    assert workspace._image == image
    assert workspace.adapter._q19_owner is owner
    assert (
        workspace.ledger.counters.get("reverse_successor_tape_width_compilations", 0)
        == 0
    )
    assert (
        workspace.ledger.counters.get("reverse_q19_primitive_pair_applications", 0)
        == pair_applications
    )
    workspace.dispose()


def test_q19_rejects_foreign_occurrence_and_rebound_source() -> None:
    left = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    right = ReverseSourceImageWorkspace(ResourceLedger(), 196, 20)
    try:
        assert left.width() == right.width()
        assert left._image is None and right._image is None
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
    primitive_pairs = counters.get("reverse_q19_primitive_pair_applications", 0)
    assert primitive_pairs >= steps - 1
    assert counters.get("source_image_primitive_applications", 0) >= steps
    assert workspace.width() == len(expected)
    assert counters.get("reverse_q19_primitive_pair_applications", 0) == primitive_pairs
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


def test_failed_successor_reconstruction_releases_traceback_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add import successor_width

    def fail_reconstruction(
        events: Sequence[Sequence[int]],
        *,
        base: int = 10,
        record_updates: Callable[[int], None] | None = None,
    ) -> tuple[int, ...]:
        del record_updates
        retained_rows = tuple(tuple(row) for row in events)
        raise ArithmeticError(f"injected reconstruction {base}: {len(retained_rows)}")

    monkeypatch.setattr(
        successor_width, "reconstruct_pair_from_live_event_suffix", fail_reconstruction
    )
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 32)
    with pytest.raises(ArithmeticError, match="injected reconstruction") as caught:
        workspace.width()
    frames = []
    current = caught.value.__traceback__
    while current is not None:
        if current.tb_frame.f_code.co_name == "fail_reconstruction":
            frames.append(current.tb_frame)
        current = current.tb_next
    assert len(frames) == 1
    assert frames[0].f_locals == {}
    scratch = [
        account
        for account in workspace.ledger.inventory()
        if account.role == "reverse_successor_width_workspace"
    ]
    assert len(scratch) == 1
    assert scratch[0].nodes == 0
    assert workspace.completed_width_if_cached() is None
    workspace.dispose()
    assert workspace.ledger.nodes == workspace.ledger.entries == 0


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
