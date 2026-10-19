"""Chronological result laws shared by primitive tile execution."""

from __future__ import annotations

from number_compiler.hashlife.execution.tile_physical_support import (
    temporal_physical_support,
)
from number_compiler.hashlife.tiles.tile_context import ResultSemantics
from number_compiler.hashlife.tiles.tile_result_records import CompletedResult


def compose_temporal_semantics(
    expected_physical_ticks: int,
    before: CompletedResult,
    after: CompletedResult,
) -> ResultSemantics:
    """Compose adjacent completed summaries in chronological order."""
    if before.physical_ticks + after.physical_ticks != expected_physical_ticks:
        raise ValueError("temporal child cocycles do not compose to their parent")
    return ResultSemantics(
        after.outgoing,
        after.outgoing_ports,
        expected_physical_ticks,
        before.event_weight + after.event_weight,
        before.frame_shift + after.frame_shift,
        after.relative_origin,
        after.relative_extent,
        observed_input_ports=after.observed_input_ports,
        physical_support=temporal_physical_support(
            before.physical_support,
            after.physical_support,
            before_ticks=before.physical_ticks,
            after_ticks=after.physical_ticks,
        ),
    )


__all__ = ["compose_temporal_semantics"]
