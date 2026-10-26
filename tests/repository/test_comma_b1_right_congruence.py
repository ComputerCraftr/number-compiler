from __future__ import annotations

from collections.abc import Hashable
from typing import TypeGuard

import pytest

from devtools.verification.comma_b1_right_congruence import (
    ActionCell,
    PartitionResult,
    refine_periodic_action_graph,
)
from devtools.verification.comma_b1_right_congruence_values import (
    is_object_tuple,
    json_report_value,
    stable_value,
)


def _assert_immediate_alias_splits_after_refinement(result: PartitionResult) -> None:
    assert result.initial_class_ids[0] == result.initial_class_ids[1]
    assert result.class_ids[0] != result.class_ids[1]


def _is_singleton_tuple(value: object) -> TypeGuard[tuple[object, ...]]:
    return is_object_tuple(value) and len(value) == 1


def test_right_congruence_refines_immediate_alias_by_successor_output() -> None:
    states = (
        "root-a",
        "root-b",
        "middle-a",
        "middle-b",
        "terminal-a",
        "terminal-b",
    )
    rows = {
        "root-a": (ActionCell(("root",), ("middle-a",), (0,)),),
        "root-b": (ActionCell(("root",), ("middle-b",), (0,)),),
        "middle-a": (ActionCell(("middle",), ("terminal-a",), (0,)),),
        "middle-b": (ActionCell(("middle",), ("terminal-b",), (0,)),),
        "terminal-a": (
            ActionCell(
                ("terminal", "a"),
            ),
        ),
        "terminal-b": (
            ActionCell(
                ("terminal", "b"),
            ),
        ),
    }

    result = refine_periodic_action_graph(
        states, rows, include_weights=False, clock_period=1
    )

    _assert_immediate_alias_splits_after_refinement(result)
    split = result.first_successor_split
    assert split is not None
    assert split["left"] == {"state": "root-a"}
    assert split["right"] == {"state": "root-b"}
    assert split["reason"] == "successor-class"
    assert split["output"] == ("root",)
    assert split["left_successor_classes"] != split["right_successor_classes"]
    assert split["successor_class_vectors_differ"] is True


def test_physical_action_weights_are_not_erased_with_control_projection() -> None:
    states = ("short", "long")
    rows: dict[str, tuple[ActionCell[str], ...]] = {
        "short": (ActionCell(("same-control",), weight=("ticks", 2)),),
        "long": (ActionCell(("same-control",), weight=("ticks", 3)),),
    }

    control = refine_periodic_action_graph(
        states, rows, include_weights=False, clock_period=1
    )
    physical = refine_periodic_action_graph(
        states, rows, include_weights=True, clock_period=1
    )

    assert control.class_ids[0] == control.class_ids[1]
    assert physical.class_ids[0] != physical.class_ids[1]


def test_receiving_phase_is_part_of_the_successor_action() -> None:
    states = ("phase-zero", "phase-one", "receiver")
    rows: dict[str, tuple[ActionCell[str], ...]] = {
        "phase-zero": (ActionCell(("continue",), ("receiver",), (0,)),),
        "phase-one": (ActionCell(("continue",), ("receiver",), (1,)),),
        "receiver": (
            ActionCell(("even-terminal",)),
            ActionCell(("odd-terminal",)),
        ),
    }

    result = refine_periodic_action_graph(
        states, rows, include_weights=False, clock_period=2
    )

    assert result.initial_class_ids[0] != result.initial_class_ids[1]
    assert result.class_ids[0] != result.class_ids[1]


def test_ordered_successor_ports_cannot_be_replaced_by_an_unordered_set() -> None:
    states = ("left-parent", "right-parent", "N-child", "Z-child")
    rows: dict[str, tuple[ActionCell[str], ...]] = {
        "left-parent": (ActionCell(("fork",), ("N-child", "Z-child"), (0, 0)),),
        "right-parent": (ActionCell(("fork",), ("Z-child", "N-child"), (0, 0)),),
        "N-child": (ActionCell(("N-result",)),),
        "Z-child": (ActionCell(("Z-result",)),),
    }

    result = refine_periodic_action_graph(
        states, rows, include_weights=False, clock_period=1
    )

    _assert_immediate_alias_splits_after_refinement(result)


def test_audit_value_normalization_handles_deep_and_recursive_containers() -> None:
    nested: Hashable = "leaf"
    for _ in range(1_200):
        nested = (nested,)

    for converted in (json_report_value(nested), stable_value(nested)):
        value = converted
        for _ in range(1_200):
            assert _is_singleton_tuple(value)
            value = value[0]
        assert value == "leaf"

    recursive: list[object] = []
    recursive.append(recursive)
    with pytest.raises(ValueError, match="recursive container"):
        json_report_value(recursive)
