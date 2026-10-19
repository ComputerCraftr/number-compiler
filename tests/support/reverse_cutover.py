"""Shared containment checks for retired reverse temporal execution paths."""

from __future__ import annotations

import importlib.util
from collections.abc import Callable, Mapping
from typing import TYPE_CHECKING, Never

import pytest

from devtools.experiments.reverse_add import uniform_projection_reference
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
    )
    from number_compiler.sequences.reverse_add.source_workspace import (
        ReverseSourceImageWorkspace,
    )


def assert_q19_output_authority(
    term: ReverseAddPoweredTerm,
) -> tuple[ReverseSourceImageWorkspace, ReversePairOutputOccurrence]:
    """Authenticate the issued decimal output independently of legacy owners."""
    from number_compiler.sequences.reverse_add.source_images import ReverseImagePayload

    workspace = term._workspace
    assert workspace is not None
    image = workspace._image
    assert image is not None
    payload = workspace.scheduler._source_image_core().view(image).payload
    assert isinstance(payload, ReverseImagePayload)
    occurrence = payload.pair_output
    assert occurrence is not None
    owner = workspace.adapter._q19_owner
    assert owner is not None
    owner.validate(occurrence)
    assert occurrence.temporal_steps == term.generation
    return workspace, occurrence


def forbid_uniform_context_compilation(
    monkeypatch: pytest.MonkeyPatch,
    forbidden: Callable[..., Never],
) -> None:
    assert importlib.util.find_spec("number_compiler.hashlife.actions.power") is None
    assert (
        importlib.util.find_spec("number_compiler.hashlife.execution.cascade_power")
        is None
    )
    assert (
        importlib.util.find_spec("number_compiler.hashlife.execution.cascade") is None
    )
    for name in (
        "uniform_successor",
        "uniform_no_growth_power",
        "edge_core_successors",
        "select_clause",
    ):
        monkeypatch.setattr(uniform_projection_reference, name, forbidden)
    monkeypatch.setattr(
        uniform_projection_reference.ProjectionClause, "instantiate", forbidden
    )


def assert_completed_child_work(counters: Mapping[str, int]) -> None:
    """Require the live completed-output producer, never retired-owner counters.

    A bounded root square need not make a parent join. Larger scheduler joins
    are independently asserted in the child-composition regression tests.
    """
    assert counters.get("reverse_q19_punctured_t2_applications", 0) > 0
    for name in (
        "source_image_primitive_applications",
        "reverse_recursive_direct_temporal_publications",
        "reverse_recursive_terminal_publications",
    ):
        assert counters.get(name, 0) == 0


def q19_application_counts(counters: Mapping[str, int]) -> tuple[int, int, int]:
    """Capture work performed by the Q19 temporal application owner."""
    return (
        counters.get("reverse_q19_punctured_t2_applications", 0),
        counters.get("reverse_q19_punctured_t4_applications", 0),
        counters.get("reverse_q19_primitive_pair_applications", 0),
    )


def assert_q19_application_counts_unchanged(
    counters: Mapping[str, int], before: tuple[int, int, int]
) -> None:
    """Check that a cached demand did not reapply its temporal action."""
    assert q19_application_counts(counters) == before


def assert_mirror_scratch_released(term: ReverseAddPoweredTerm) -> None:
    """Both mirror consumers return their shared buffer and reservation."""
    scratch = term._mirror_output_scratch
    assert scratch is not None and not scratch
    account = next(
        item for item in term.resource_ledger.inventory() if item.owner == scratch.owner
    )
    assert account.entries == account.nodes == account.accounting_delta == 0
