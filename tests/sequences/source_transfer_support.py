"""Common assertions for finite owner-bound source transfer packets."""

from __future__ import annotations

from collections.abc import Mapping
from typing import cast


def assert_exact_source_transfer_path(
    packet: Mapping[str, object],
    expected_path: tuple[tuple[int, int], ...],
    *,
    physical_interval: tuple[int, int],
    border_span: int,
    pair_coordinate_order: tuple[str, str],
) -> None:
    assert packet["status"] == "available"
    assert packet["physical_interval"] == physical_interval
    assert packet["source_pair_path"] == expected_path
    assert packet["pair_coordinate_order"] == pair_coordinate_order
    assert packet["exact_completed_children_joined"] is True
    assert packet["source_guard_applied_before_matrix_composition"] is True
    assert packet["physical_repeat_certified"] is False
    assert packet["future_repetition_claimed"] is False

    matrices = cast(tuple[tuple[int, ...], ...], packet["phase_matrices"])
    phases = cast(tuple[dict[str, object], ...], packet["border_phases"])
    assert len(matrices) == len(expected_path) - 1
    assert len(phases) == len(expected_path) - 1
    for index, rows in enumerate(matrices):
        source_pair, target_pair = expected_path[index : index + 2]
        source_index = 10 * source_pair[0] + source_pair[1]
        target_index = 10 * target_pair[0] + target_pair[1]
        assert rows[source_index] == 1 << target_index
        assert sum(row != 0 for row in rows) == 1
    for phase in phases:
        interval = cast(tuple[int, int], phase["physical_interval"])
        assert interval[1] - interval[0] == border_span
