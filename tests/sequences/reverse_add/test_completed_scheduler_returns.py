"""Nondecimal recursive publications retain the admitted reverse occurrence.

Decimal producer no-replay gates remain in test_source_images and the public
cutover tests; this module exercises the distinct recursive field-image owner.
"""

from __future__ import annotations

from dataclasses import replace
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageDemand,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_images import (
    ReverseImagePayload,
    ReverseSourceImageWorkspace,
    _ReverseSourceImageAdapter,
)
from tests.support.reference_arithmetic import literal_reverse_add_digits


def _forbid_reconstruction(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("completed provider was reconstructed from its source")


def _view(workspace: ReverseSourceImageWorkspace, steps: int) -> SourceImageView:
    image = workspace.scheduler.source_image(
        workspace.adapter, workspace.source, workspace.actions.action(steps)
    )
    return workspace.scheduler._source_image_core().view(image)


def _expected(steps: int) -> tuple[int, ...]:
    return literal_reverse_add_digits(1, steps, 3)


def test_scheduler_extends_completed_return_without_source_reconstruction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 1, 20, base=3)
    first = _view(workspace, 4)
    assert isinstance(first.payload, ReverseImagePayload)
    assert first.payload.occurrence is not None
    cutover = workspace.adapter._recursive
    assert cutover is not None
    monkeypatch.setattr(cutover, "pair_image", _forbid_reconstruction)
    for steps in (8, 16, 20):
        view = _view(workspace, steps)
        assert isinstance(view.payload, ReverseImagePayload)
        assert view.payload.occurrence is not None
        expected = _expected(steps)
        for i, digit in enumerate(expected):
            assert (
                workspace.scheduler.source_projection(
                    workspace.adapter, view.identity, SourceImageDemand("digit", (i,))
                ).value
                == digit
            )
    assert (
        workspace.ledger.counters["reverse_source_completed_prefix_applications"] == 3
    )


def test_scheduler_child_chronology_consumes_completed_provider(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 1, 16, base=3)
    original = workspace.adapter.apply_composite
    action = workspace.actions.action(8)

    def descend(
        action_arg: object, source: SourceImageView, demand: SourceImageDemand | None
    ) -> object:
        if action_arg == action and source.binding.extent == 0:
            return None
        return original(action_arg, source, demand)

    monkeypatch.setattr(workspace.adapter, "apply_composite", descend)
    result = _view(workspace, 8)
    assert workspace.ledger.counters["source_image_chronological_compositions"] == 1
    assert (
        workspace.ledger.counters["reverse_source_completed_provider_applications"] == 1
    )
    assert workspace.adapter.project(result, SourceImageDemand("width")).value == len(
        _expected(8)
    )


@pytest.mark.parametrize("evict", (False, True))
def test_complete_parent_hit_does_not_descend_again(
    monkeypatch: pytest.MonkeyPatch,
    evict: bool,
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 1, 16, base=3)
    before = _view(workspace, 4)
    after = _view(workspace, 8)
    cutover = workspace.adapter._recursive
    assert cutover is not None
    if evict:
        workspace.ledger.evict_query_memos()
    monkeypatch.setattr(cutover, "apply_to_occurrence", _forbid_reconstruction)
    candidate = workspace.adapter.apply_composite(
        workspace.actions.action(4), before, None
    )
    assert candidate is not None and candidate.payload == after.payload
    assert workspace.ledger.counters["reverse_source_completed_parent_hits"] == 1


@pytest.mark.parametrize("damage", ("foreign", "missing", "action", "source"))
def test_completed_payload_rejects_foreign_or_mismatched_authority(damage: str) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 1, 16, base=3)
    view = _view(workspace, 4)
    assert isinstance(view.payload, ReverseImagePayload)
    original = view.payload
    if damage == "foreign":
        other = ReverseSourceImageWorkspace(ResourceLedger(), 1, 16, base=3)
        payload = _view(other, 4).payload
        assert isinstance(payload, ReverseImagePayload)
        view = replace(view, payload=replace(original, occurrence=payload.occurrence))
    elif damage == "missing":
        view = replace(view, payload=replace(original, occurrence=None))
    elif damage == "action":
        view = replace(
            view, payload=replace(original, action=workspace.actions.action(8))
        )
    else:
        other = ReverseSourceImageWorkspace(ResourceLedger(), 2, 16, base=3)
        view = replace(view, binding=replace(view.binding, source=other.source))
    with pytest.raises(ValueError):
        workspace.adapter.project(view, SourceImageDemand("width"))


def test_cached_occurrence_validates_source_before_returning() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 1, 16, base=3)
    _view(workspace, 4)
    other = ReverseSourceImageWorkspace(ResourceLedger(), 2, 16, base=3)
    with pytest.raises(ValueError, match="source changed"):
        workspace.adapter._recursive_occurrence(other.actions.source(other.source), 4)


@pytest.mark.parametrize("cached_steps", (4, 8))
def test_occurrence_memo_rejects_duration_alias(cached_steps: int) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 1, 16, base=3)
    _view(workspace, 4)
    adapter = workspace.adapter
    occurrence = adapter._recursive_occurrences[4]
    adapter._recursive_occurrences[cached_steps] = replace(occurrence, temporal_steps=2)
    source = workspace.actions.source(workspace.source)
    with pytest.raises(ValueError, match="duration"):
        adapter._recursive_occurrence(source, 8)


def test_prepared_authority_cannot_change_before_first_construction() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 1, 16, base=3)
    other = ReverseSourceImageWorkspace(ResourceLedger(), 2, 16, base=3)
    assert workspace.adapter._recursive is None
    with pytest.raises(ValueError, match="source or horizon changed"):
        workspace.adapter.prepare_recursive_authority(
            other.actions.source(other.source), 16
        )


@pytest.mark.parametrize("composite", (False, True))
@pytest.mark.parametrize("damage", ("extent", "ports", "precision"))
def test_direct_application_validates_input_binding(
    composite: bool, damage: str
) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 1, 16, base=3)
    original = _view(workspace, 0)
    binding = original.binding
    if damage == "extent":
        binding = replace(binding, extent=1)
    elif damage == "ports":
        binding = replace(binding, boundary_ports=())
    else:
        binding = replace(binding, precision=None)
    forged = replace(original, binding=binding)
    with pytest.raises(ValueError, match="binding disagree"):
        if composite:
            workspace.adapter.apply_composite(workspace.actions.action(4), forged, None)
        else:
            workspace.adapter.apply_primitive(workspace.actions.primitive, forged)


def test_identity_preserves_completed_input_contract() -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 1, 16, base=3)
    for steps in (0, 1, 2, 4):
        source = _view(workspace, steps)
        candidate = workspace.adapter.apply_primitive(
            workspace.actions.identity, source
        )
        assert candidate.payload == source.payload
        assert candidate.extent == source.binding.extent
        assert candidate.boundary_ports == source.binding.boundary_ports
        assert candidate.precision == source.binding.precision


@pytest.mark.parametrize("damage", ("extent", "ports", "precision", "source"))
def test_failure_observer_authenticates_the_complete_binding(damage: str) -> None:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 1, 16, base=3)
    other = ReverseSourceImageWorkspace(ResourceLedger(), 2, 16, base=3)
    try:
        view = _view(workspace, 4)
        workspace.adapter.first_failure(view)
        binding = view.binding
        if damage == "extent":
            binding = replace(binding, extent=8)
        elif damage == "ports":
            binding = replace(binding, boundary_ports=(0,))
        elif damage == "precision":
            binding = replace(binding, precision=1)
        else:
            binding = replace(binding, source=other.source)
        with pytest.raises(ValueError):
            workspace.adapter.first_failure(replace(view, binding=binding))
    finally:
        workspace.dispose()
        other.dispose()


def test_failed_preparation_disposes_the_unregistered_adapter(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()

    def failed_preparation(
        adapter: _ReverseSourceImageAdapter,
        source: ExactSource,
        steps: int,
        construction: OriginalSourceConstruction | None = None,
    ) -> Never:
        assert adapter.ports(source).terminal == 0
        assert ledger.entries > 0
        raise LookupError("preparation failed before adapter registration")

    monkeypatch.setattr(
        _ReverseSourceImageAdapter, "prepare_recursive_authority", failed_preparation
    )
    with pytest.raises(LookupError, match="before adapter registration"):
        ReverseSourceImageWorkspace(ledger, 1, 16, base=3)
    assert ledger.entries == ledger.nodes == 0
