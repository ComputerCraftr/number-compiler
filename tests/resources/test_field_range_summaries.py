"""Exact occurrence ranges cannot borrow foreign or local-presence expressions."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.hashlife.execution.continuations.higher_types import FieldAtomSort
from number_compiler.hashlife.execution.field_image_summaries import (
    ParametricFieldImageSummary,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveTemporalCutover,
)


@pytest.fixture
def admitted_range() -> tuple[
    ReverseRecursiveTemporalCutover, ParametricFieldImageSummary
]:
    owner = ReverseRecursiveTemporalCutover(
        ResourceLedger(), (8, 1), base=10, maximum_steps=4
    )
    occurrence = owner.pair_image(2)
    summary = owner.images.resolve(occurrence.image).summary
    assert isinstance(summary, ParametricFieldImageSummary)
    assert summary.range_summary is not None
    return owner, summary


def test_complete_range_validates_without_evaluating_outputs(
    admitted_range: tuple[ReverseRecursiveTemporalCutover, ParametricFieldImageSummary],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    owner, summary = admitted_range

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("range validation evaluated a future output")

    monkeypatch.setattr(owner.semantics, "evaluate", forbidden)
    monkeypatch.setattr(owner.outputs, "observe_extent", forbidden)
    summary.validate_range(owner.interfaces)


@pytest.mark.parametrize("corruption", ("foreign", "unallocated", "sort", "free"))
def test_range_rejects_incompatible_handles_before_consumption(
    admitted_range: tuple[ReverseRecursiveTemporalCutover, ParametricFieldImageSummary],
    corruption: str,
) -> None:
    owner, summary = admitted_range
    original = summary.range_summary
    assert original is not None
    if corruption == "foreign":
        other = ReverseRecursiveTemporalCutover(
            ResourceLedger(), (2, 1), base=10, maximum_steps=4
        )
        image = other.pair_image(2)
        foreign = other.images.resolve(image.image).summary
        assert isinstance(foreign, ParametricFieldImageSummary)
        damaged = replace(summary, range_summary=foreign.range_summary)
    else:
        expression = (
            replace(original.extent, local_id=10**9)
            if corruption == "unallocated"
            else original.activity
            if corruption == "sort"
            else owner.semantics.variable(
                FieldAtomSort("field-active-extent", summary.extent_bound + 1),
                "unbound-range",
            )
        )
        damaged = replace(summary, range_summary=replace(original, extent=expression))
    with pytest.raises((TypeError, ValueError)):
        damaged.validate_range(owner.interfaces)
