"""Completed reverse images preserve a live first blank and blank tail."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.recursive_cutover import (
    ReverseRecursiveTemporalCutover,
)


def test_completed_children_keep_first_blank_seam_and_source_authority(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cutover = ReverseRecursiveTemporalCutover(
        ResourceLedger(), (9, 9, 9, 9), base=10, maximum_steps=4
    )
    action = cutover.pair_action(2)
    source = cutover.source
    left_source, right_source = cutover.sources.children(source)
    left_geometry = cutover.geometries.child(cutover.geometry, 0)
    right_geometry = cutover.geometries.child(cutover.geometry, 1)

    root_signature = cutover.adapter.signature(action, cutover.geometry)
    left_signature = cutover.adapter.signature(action, left_geometry)
    right_signature = cutover.adapter.signature(action, right_geometry)
    left_image = cutover.executor.image(
        action, left_source, left_geometry, left_signature
    )
    right_image = cutover.executor.image(
        action, right_source, right_geometry, right_signature
    )
    cutover._boundaries(action)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("completed parent join replayed primitive semantics")

    for name in ("step", "emit", "boundary"):
        monkeypatch.setattr(cutover.runtime, name, forbidden)
    monkeypatch.setattr(cutover.adapter, "_compile", forbidden)

    joins_before = cutover.ledger.counters.get(
        "reverse_recursive_completed_child_joins", 0
    )
    image = cutover.executor.image(action, source, cutover.geometry, root_signature)
    assert cutover.ledger.counters["reverse_recursive_completed_child_joins"] == (
        joins_before + 1
    )

    record = cutover.images.resolve(image)
    assert record.left == left_image
    assert record.right == right_image
    summary = record.summary
    range_summary = getattr(summary, "range_summary", None)
    assert range_summary is not None

    recovered = cutover.adapter._macro_from_completed(
        image, source, action, cutover.geometry, None
    )
    for name in ("activity", "first_active", "last_active", "extent", "growth"):
        assert getattr(range_summary, name) == getattr(recovered, name)
    assert recovered.source_extent == 4
    assert recovered.width == cutover.extent == 8

    boundaries = cutover._boundaries(action)
    bound = cutover.outputs._inputs(recovered.interface, *boundaries)
    local_extent = cutover.interfaces.resolve(recovered.interface).components.extent
    assert isinstance(local_extent, HigherExpressionID)
    assert cutover.semantics.evaluate(recovered.extent, bound) == 5
    assert cutover.semantics.evaluate(local_extent, bound) == 1

    occurrence = cutover._new_occurrence(image, action, 2, None)
    cutover.validate_occurrence(occurrence)
    assert cutover.pair_width(occurrence) == 5
    assert tuple(cutover._pair_stream(occurrence, cutover.extent)) == (
        9,
        18,
        18,
        18,
        9,
        19,
        19,
        19,
    )

    foreign_source = right_source
    with pytest.raises(ValueError, match="not published for this occurrence"):
        cutover.images.validate_occurrence(left_image, foreign_source, action)
