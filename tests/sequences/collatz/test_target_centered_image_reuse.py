"""Exact occurrence translations cannot alias a centered Collatz action."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.skew_transfer import (
    integer_dyadic_fiber_action,
)
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnImageID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)
from tests.support.reference_arithmetic import collatz_literal as _literal


def _apply(
    workspace: CollatzPhysicalImageWorkspace, residue: int, width: int, lift: int
) -> int:
    source = workspace.admitted_source(residue + (lift << width), width)
    action = workspace.action_for_extent(width)
    image = workspace.scheduler.source_image(workspace, source, action)
    payload = workspace.scheduler.source_image_view(workspace, image).payload
    assert type(payload) is DyadicReturnImageID
    summary = workspace.image_node(payload).summary
    chart = integer_dyadic_fiber_action(summary.transfer, residue, width)
    return chart.addend + chart.multiplier * lift


def test_exact_run_translation_is_bound_to_its_high_fiber() -> None:
    workspace = CollatzPhysicalImageWorkspace(
        ResourceLedger(), 27, 0, retain_chronology=False
    )
    # Both sources lie above the terminal cycle and share the same eight low
    # bits. The run constructor emits a constant exact endpoint for each.
    first = 27 + 256 * 8
    second = 27 + 256 * 9
    assert _apply(workspace, 27, 8, 8) == _literal(first, 8)
    assert _apply(workspace, 27, 8, 9) == _literal(second, 8)
    assert _literal(first, 8) != _literal(second, 8)
    assert workspace.ledger.counters.get("source_image_relative_transfer_hits", 0) == 0


def test_balanced_complete_effect_still_reuses_a_low_cylinder() -> None:
    workspace = CollatzPhysicalImageWorkspace(
        ResourceLedger(), 27, 0, retain_chronology=False
    )
    width = 129
    # A nonroot broad cylinder may use the balanced complete effect even when
    # one exact high fiber has a root-only decimal border route.
    first = 27 + (8 << width)
    second = 27 + (9 << width)
    assert _apply(workspace, 27, width, 8) == _literal(first, width)
    before = workspace.ledger.counters.get("source_image_relative_transfer_hits", 0)
    routing_before = workspace.ledger.counters[
        "collatz_physical_temporal_reuse_routing_operand_bits"
    ]
    assert _apply(workspace, 27, width, 9) == _literal(second, width)
    assert (
        workspace.ledger.counters["source_image_relative_transfer_hits"] == before + 1
    )
    assert (
        workspace.ledger.counters[
            "collatz_physical_temporal_reuse_routing_operand_bits"
        ]
        > routing_before
    )
    assert all(
        row.nodes == 0
        for row in workspace.ledger.inventory()
        if row.role == "run_arithmetic_workspace"
    )


def test_direct_reuse_cannot_bypass_the_exact_run_key() -> None:
    workspace = CollatzPhysicalImageWorkspace(
        ResourceLedger(), 27, 0, retain_chronology=False
    )
    action = workspace.action_for_extent(8)
    first = workspace.admitted_source(27 + (8 << 8), 8)
    second = workspace.admitted_source(27 + (9 << 8), 8)
    first_origin = workspace.scheduler.source_image_view(
        workspace, workspace.scheduler.source_image_origin(workspace, first)
    )
    second_origin = workspace.scheduler.source_image_view(
        workspace, workspace.scheduler.source_image_origin(workspace, second)
    )
    first_result = workspace.scheduler.source_image_view(
        workspace, workspace.scheduler.source_image(workspace, first, action)
    )
    with pytest.raises(ValueError, match="same admitted cylinder"):
        workspace.transport_reuse(action, first_origin, first_result, second_origin)
