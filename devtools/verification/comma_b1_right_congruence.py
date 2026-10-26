"""Finite weighted right-congruence census for the exact comma source graph.

The census starts from the executable SemanticContinuationArena. It does not
consult candidate ranks, terminal tables, or an asserted quotient size. Source
phase rows remain compressed by their local periods; all completed B1 source
continuations are evaluated over their bounded receiving-clock domains.

Every result is a developer audit. Class numbers are local to one report and
do not authenticate a source binding or authorize a production cutover.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from collections.abc import Hashable, Mapping, Sequence
from dataclasses import dataclass
from math import lcm
from typing import Generic, TypeVar

from number_compiler.arithmetic.functions.finite_observer import (
    class_members,
    minimize_finite_observer,
)
from number_compiler.sequences.comma.boundary_chart import (
    PERIOD,
    BoundaryChart,
)
from number_compiler.sequences.comma.semantic_continuation import (
    SemanticContinuation,
    WeightedAction,
)
from number_compiler.sequences.comma.symbolic_return import least_cyclic_rotation

from .comma_b1_quotient import offset_orbit
from .comma_b1_right_congruence_values import (
    json_report_value as _json_value,
)
from .comma_b1_right_congruence_values import (
    stable_value as _stable_value,
)
from .comma_b1_right_congruence_values import (
    state_record as _state_record,
)
from .comma_b1_source_continuation import (
    canonical_roots,
    production_semantic_owner,
)

StateT = TypeVar("StateT", bound=Hashable)
ItemT = TypeVar("ItemT")


@dataclass(frozen=True, slots=True)
class ActionCell(Generic[StateT]):
    """One exact phase-selected action and its ordered continuation edges."""

    observation: tuple[Hashable, ...]
    successors: tuple[StateT, ...] = ()
    phase_deltas: tuple[int, ...] = ()
    weight: tuple[Hashable, ...] = ()


@dataclass(frozen=True, slots=True)
class PartitionResult:
    """A finite stable partition with its immediate-output baseline."""

    states: tuple[Hashable, ...]
    class_ids: tuple[int, ...]
    initial_class_ids: tuple[int, ...]
    rounds: int
    first_successor_split: Mapping[str, object] | None
    phase_class_profiles: tuple[tuple[int, ...], ...] = ()

    @property
    def class_count(self) -> int:
        return len(set(self.class_ids))


def _primitive_period(values: tuple[ItemT, ...]) -> tuple[ItemT, ...]:
    """Keep exact phase origin while removing a repeated local suffix."""
    if not values:
        raise ValueError("periodic action row cannot be empty")
    length = len(values)
    for candidate in range(1, length + 1):
        if length % candidate == 0 and all(
            values[index] == values[index % candidate] for index in range(length)
        ):
            return values[:candidate]
    raise AssertionError("finite periodic row has no primitive period")


def _classify(signatures: Sequence[Hashable]) -> tuple[int, ...]:
    identifiers: dict[Hashable, int] = {}
    return tuple(
        identifiers.setdefault(signature, len(identifiers)) for signature in signatures
    )


def refine_periodic_action_graph(
    states: tuple[StateT, ...],
    rows: Mapping[StateT, tuple[ActionCell[StateT], ...]],
    *,
    include_weights: bool,
    clock_period: int | None = None,
) -> PartitionResult:
    """Compute a stable phase-aligned right congruence from periodic rows.

    Input rows stay locally compressed. The temporary refinement universe is
    ``state × clock phase`` so an edge into a child with a longer local period
    is evaluated at its actual receiving phase. Absolute phase is omitted from
    observations: it is occurrence data, and the product graph carries the
    receiving phase through each edge.
    """
    if not states or len(set(states)) != len(states) or set(rows) != set(states):
        raise ValueError("action graph states and row owners must be exact and unique")
    state_set = set(states)
    for state in states:
        row = rows[state]
        if not row:
            raise ValueError("right-congruence graph contains an empty row")
        for cell in row:
            if len(cell.successors) != len(cell.phase_deltas):
                raise ValueError("action successor transports are malformed")
            if any(target not in state_set for target in cell.successors):
                raise ValueError("action successor leaves the declared graph")
    natural_period = lcm(*(len(rows[state]) for state in states))
    phase_count = natural_period if clock_period is None else clock_period
    if type(phase_count) is not int or phase_count < 1 or phase_count % natural_period:
        raise ValueError("clock period must be a positive multiple of every row period")

    state_indices = {state: index for index, state in enumerate(states)}
    max_successors = max(
        len(cell.successors) for state in states for cell in rows[state]
    )
    expanded_rows: list[tuple[int | None, ...]] = []
    expanded_outputs: list[int] = []
    output_ids: dict[Hashable, int] = {}
    immediate_profiles: list[tuple[Hashable, ...]] = []
    for source_index, state in enumerate(states):
        profile: list[Hashable] = []
        row = rows[state]
        for phase in range(phase_count):
            cell = row[phase % len(row)]
            output: Hashable = (
                cell.observation,
                cell.phase_deltas,
                cell.weight if include_weights else (),
            )
            output_id = output_ids.setdefault(output, len(output_ids))
            profile.append(
                (
                    cell.observation,
                    cell.phase_deltas,
                    cell.weight if include_weights else (),
                )
            )
            edges: list[int | None] = []
            for target, phase_delta in zip(
                cell.successors, cell.phase_deltas, strict=True
            ):
                target_index = state_indices[target]
                target_phase = (phase + phase_delta) % phase_count
                edges.append(target_index * phase_count + target_phase)
            edges.extend([None] * (max_successors - len(edges)))
            expanded_rows.append(tuple(edges))
            expanded_outputs.append(output_id)
        if source_index != len(immediate_profiles):
            raise AssertionError("source phase profiles lost their owner order")
        immediate_profiles.append(tuple(profile))

    minimized = minimize_finite_observer(expanded_rows, expanded_outputs)
    stable_profiles = tuple(
        tuple(
            minimized.class_ids[source_index * phase_count + phase]
            for phase in range(phase_count)
        )
        for source_index in range(len(states))
    )
    return PartitionResult(
        tuple(states),
        _classify(stable_profiles),
        _classify(tuple(immediate_profiles)),
        minimized.rounds,
        _phase_split_witness(
            tuple(states),
            rows,
            tuple(immediate_profiles),
            stable_profiles,
            minimized.class_ids,
            phase_count,
            max_successors,
            state_indices,
            include_weights=include_weights,
        ),
        stable_profiles,
    )


def _phase_split_witness(
    states: tuple[StateT, ...],
    rows: Mapping[StateT, tuple[ActionCell[StateT], ...]],
    immediate_profiles: tuple[tuple[Hashable, ...], ...],
    stable_profiles: tuple[tuple[int, ...], ...],
    phase_class_ids: tuple[int, ...],
    phase_count: int,
    max_successors: int,
    state_indices: Mapping[StateT, int],
    *,
    include_weights: bool,
) -> Mapping[str, object] | None:
    """Find an immediate-output alias separated by a later successor."""
    immediate_classes = _classify(immediate_profiles)
    stable_classes = _classify(stable_profiles)
    grouped: dict[int, list[int]] = {}
    for index, class_id in enumerate(immediate_classes):
        grouped.setdefault(class_id, []).append(index)
    for members in grouped.values():
        first_by_stable: dict[int, int] = {}
        pair: tuple[int, int] | None = None
        for index in members:
            prior = first_by_stable.setdefault(stable_classes[index], index)
            if prior != index:
                continue
            if len(first_by_stable) > 1:
                pair = (next(iter(first_by_stable.values())), index)
                break
        if pair is None:
            continue
        left_index, right_index = pair
        left_state, right_state = states[left_index], states[right_index]
        for phase in range(phase_count):
            left = rows[left_state][phase % len(rows[left_state])]
            right = rows[right_state][phase % len(rows[right_state])]
            if (
                left.observation,
                left.phase_deltas,
                left.weight if include_weights else (),
            ) != (
                right.observation,
                right.phase_deltas,
                right.weight if include_weights else (),
            ):
                continue
            left_targets: tuple[int | None, ...] = tuple(
                phase_class_ids[
                    state_indices[target] * phase_count + (phase + delta) % phase_count
                ]
                for target, delta in zip(
                    left.successors, left.phase_deltas, strict=True
                )
            )
            right_targets: tuple[int | None, ...] = tuple(
                phase_class_ids[
                    state_indices[target] * phase_count + (phase + delta) % phase_count
                ]
                for target, delta in zip(
                    right.successors, right.phase_deltas, strict=True
                )
            )
            if left_targets == right_targets:
                continue
            left_targets += (None,) * (max_successors - len(left_targets))
            right_targets += (None,) * (max_successors - len(right_targets))
            return {
                "left": _state_record(left_state),
                "right": _state_record(right_state),
                "phase": phase,
                "reason": "successor-class",
                "output": _json_value(left.observation),
                "left_successor_classes": left_targets,
                "right_successor_classes": right_targets,
                "successor_class_vectors_differ": (
                    stable_profiles[left_index] != stable_profiles[right_index]
                ),
            }
    return None


def _occurrence_weight(weighted: WeightedAction) -> tuple[Hashable, ...]:
    occurrence = weighted.occurrence
    return (
        occurrence.entry_period,
        occurrence.entry_displacement,
        occurrence.near_physical_steps,
        occurrence.literal_increment,
        occurrence.exponent_advance,
        occurrence.live_coordinate,
    )


def _physical_fragment(weighted: WeightedAction) -> tuple[Hashable, ...]:
    """Retain one exact ordered action fragment and its occurrence payload."""
    action = weighted.control
    if action.kind == "goto":
        if weighted.child is None or action.target is None:
            raise AssertionError("physical Goto fragment lost its exact child")
        control: tuple[Hashable, ...] = ("goto", _stable_value(weighted.child))
    elif action.kind == "live":
        if action.live_root is None:
            raise AssertionError("physical Live fragment lost its exact root")
        control = ("live", action.live_root, action.exponent_advance)
    elif action.kind == "stop":
        if action.stop_j is None:
            raise AssertionError("physical Stop fragment lost its exact position")
        control = ("stop", action.stop_j)
    elif action.kind == "identity":
        control = ("identity",)
    else:
        raise AssertionError("unknown physical comma action")
    return (control, _occurrence_weight(weighted))


def _root_binding(
    root_sources: tuple[BoundaryChart, ...],
) -> dict[int, BoundaryChart]:
    return {offset_orbit(source.coordinate): source for source in root_sources}


def _source_action_rows(
    view: SemanticContinuation,
    root_sources: tuple[BoundaryChart, ...],
) -> dict[BoundaryChart, tuple[ActionCell[BoundaryChart], ...]]:
    roots = _root_binding(root_sources)
    rows: dict[BoundaryChart, tuple[ActionCell[BoundaryChart], ...]] = {}
    for source, source_row in view.transitions.items():
        period = view.periods[source]
        if period != len(source_row) or PERIOD % period:
            raise AssertionError("source action row lost its exact divisor clock")
        cells: list[ActionCell[BoundaryChart]] = []
        for weighted in source_row:
            action = weighted.control
            successors: tuple[BoundaryChart, ...] = ()
            phase_deltas: tuple[int, ...] = ()
            if action.kind == "goto":
                child = weighted.child
                if child is None or view.source_ids.get(child) != action.target:
                    raise AssertionError("Goto lost its authenticated source binding")
                observation: tuple[Hashable, ...] = ("goto",)
                successors = (child,)
                phase_deltas = (0,)
            elif action.kind == "live":
                if action.live_root is None:
                    raise AssertionError("Live action lost its exact root")
                fiber = offset_orbit(action.live_root)
                successor = roots.get(fiber)
                if successor is None:
                    raise AssertionError("Live root is outside the compiled roots")
                observation = (
                    "live",
                    action.live_root,
                    action.exponent_advance,
                    fiber,
                )
                successors = (successor,)
                phase_deltas = (action.exponent_advance,)
            elif action.kind == "stop":
                if action.stop_j is None:
                    raise AssertionError("Stop action lost its exact local position")
                if action.stop_j == 8:
                    observation = ("landmine", action.stop_j, ())
                else:
                    fork_a = action.stop_j + 2
                    if source.delta != 0:
                        raise AssertionError("fork source has an unnormalized clock")
                    observation = (
                        "fork",
                        fork_a,
                        (("N", fork_a, 0), ("Z", fork_a, 0)),
                    )
            elif action.kind == "identity":
                observation = ("identity",)
            else:
                raise AssertionError("unknown semantic continuation action")
            cells.append(
                ActionCell(
                    observation,
                    successors,
                    phase_deltas,
                    _occurrence_weight(weighted),
                )
            )
        rows[source] = tuple(cells)
    return rows


def _reachable_local_period(view: SemanticContinuation, root: BoundaryChart) -> int:
    pending = [root]
    visited: set[BoundaryChart] = set()
    period = 1
    while pending:
        source = pending.pop()
        if source in visited:
            continue
        visited.add(source)
        period = lcm(period, view.periods[source])
        if PERIOD % period:
            raise AssertionError("reachable action clock escaped the 924-period")
        for item in view.transitions[source]:
            if item.control.kind == "goto":
                if item.child is None:
                    raise AssertionError("completed B1 path lost a Goto source")
                pending.append(item.child)
    return period


def _resolve_completed_action(
    view: SemanticContinuation,
    roots: Mapping[int, BoundaryChart],
    source: BoundaryChart,
    phase: int,
) -> tuple[ActionCell[BoundaryChart], tuple[tuple[Hashable, ...], ...]]:
    current = source
    visited: set[BoundaryChart] = set()
    weight_trace: list[tuple[Hashable, ...]] = []
    while True:
        if current in visited:
            raise AssertionError("internal Goto continuation is cyclic")
        visited.add(current)
        row = view.transitions.get(current)
        if row is None:
            raise AssertionError("internal continuation left its exact graph")
        item = row[phase % len(row)]
        weight_trace.append(_physical_fragment(item))
        action = item.control
        if action.kind == "goto":
            child = item.child
            if child is None or view.source_ids.get(child) != action.target:
                raise AssertionError("completed B1 Goto lost its checked child")
            if item.occurrence.exponent_advance != 0:
                raise AssertionError("internal Goto changed the exponent clock")
            current = child
            continue
        if action.kind == "live":
            if action.live_root is None:
                raise AssertionError("completed Live action lost its exact root")
            fiber = offset_orbit(action.live_root)
            successor = roots.get(fiber)
            if successor is None:
                raise AssertionError("completed Live root is not source-admitted")
            if action.exponent_advance != 1:
                raise AssertionError("completed Live action lost its phase advance")
            return (
                ActionCell(
                    (
                        "live",
                        action.live_root,
                        fiber,
                        ("entry-root", successor.coordinate),
                        action.exponent_advance,
                    ),
                    (successor,),
                    (action.exponent_advance,),
                ),
                tuple(weight_trace),
            )
        if action.kind == "stop":
            if action.stop_j is None:
                raise AssertionError("completed Stop lost its local position")
            if action.stop_j == 8:
                return (
                    ActionCell(("landmine", 8, current.delta)),
                    tuple(weight_trace),
                )
            fork_a = action.stop_j + 2
            children = (
                ("N", fork_a, current.delta),
                ("Z", fork_a, current.delta),
            )
            return (
                ActionCell(("fork", fork_a, children, current.delta)),
                tuple(weight_trace),
            )
        if action.kind == "identity":
            return ActionCell(("identity",)), tuple(weight_trace)
        raise AssertionError("completed B1 action did not terminate")


def _completed_source_rows(
    view: SemanticContinuation,
    states: tuple[BoundaryChart, ...],
    roots: tuple[BoundaryChart, ...],
) -> dict[BoundaryChart, tuple[ActionCell[BoundaryChart], ...]]:
    root_map = _root_binding(roots)
    rows: dict[BoundaryChart, tuple[ActionCell[BoundaryChart], ...]] = {}
    for source in states:
        upper_period = _reachable_local_period(view, source)
        cells: list[ActionCell[BoundaryChart]] = []
        for phase in range(upper_period):
            cell, weights = _resolve_completed_action(view, root_map, source, phase)
            cell = ActionCell(
                cell.observation,
                cell.successors,
                cell.phase_deltas,
                tuple(weights),
            )
            cells.append(cell)
        pattern = _primitive_period(tuple(cells))
        if PERIOD % len(pattern):
            raise AssertionError("completed B1 action has an unproved clock period")
        rows[source] = pattern
    return rows


def _partition_summary(
    result: PartitionResult,
) -> dict[str, object]:
    groups = class_members(result.class_ids, result.class_count)
    size_histogram = Counter(map(len, groups))
    non_singleton = tuple(
        {
            "class": class_id,
            "members": tuple(_state_record(result.states[index]) for index in group),
        }
        for class_id, group in enumerate(groups)
        if len(group) > 1
    )
    encoded_states = tuple(_state_record(state) for state in result.states)
    return {
        "state_count": len(result.states),
        "class_count": result.class_count,
        "initial_output_class_count": len(set(result.initial_class_ids)),
        "refinement_rounds": result.rounds,
        "class_size_histogram": dict(sorted(size_histogram.items())),
        "non_singleton_classes": non_singleton,
        "state_to_class": tuple(
            {"state": encoded_states[index], "class": class_id}
            for index, class_id in enumerate(result.class_ids)
        ),
        "first_successor_split": result.first_successor_split,
        "phase_aligned_state_class_count": result.class_count,
        "common_phase_translation_class_count": (
            _translated_profile_class_count(result.phase_class_profiles)
            if result.phase_class_profiles
            else None
        ),
    }


def _profile_partitions(
    profiles: Sequence[tuple[Hashable, ...]],
) -> dict[str, object]:
    if not profiles or any(len(profile) != PERIOD for profile in profiles):
        raise ValueError("return profiles must cover the complete 924-phase clock")
    exact_ids = _classify(profiles)
    rotations: list[tuple[int, tuple[Hashable, ...]]] = []
    for profile in profiles:
        row_keys = tuple(repr(value) for value in profile)
        start = least_cyclic_rotation(
            PERIOD,
            row_keys.__getitem__,
            compare=_compare_text,
        )
        rotations.append((start, profile[start:] + profile[:start]))
    translated_ids = _classify(tuple(row for _, row in rotations))
    groups = class_members(exact_ids, len(set(exact_ids)))
    translated_groups = class_members(translated_ids, len(set(translated_ids)))
    shifts: list[dict[str, int]] = []
    for group in translated_groups:
        representative = group[0]
        representative_start = rotations[representative][0]
        for member in group[1:]:
            member_start = rotations[member][0]
            shifts.append(
                {
                    "representative_index": representative,
                    "member_index": member,
                    "member_receiving_phase_shift": (
                        representative_start - member_start
                    )
                    % PERIOD,
                }
            )
            shift = (representative_start - member_start) % PERIOD
            if any(
                profiles[member][phase]
                != profiles[representative][(phase + shift) % PERIOD]
                for phase in range(PERIOD)
            ):
                raise AssertionError("common clock shift failed exact return rows")
    return {
        "phase_aligned_class_count": len(groups),
        "common_clock_translation_class_count": len(translated_groups),
        "translation_merges": len(groups) - len(translated_groups),
        "phase_aligned_classes": groups,
        "common_clock_translation_classes": translated_groups,
        "translation_witnesses": tuple(shifts),
        "clock_phase_is_occurrence_data": True,
    }


def _translated_profile_class_count(
    profiles: tuple[tuple[int, ...], ...],
) -> int:
    if not profiles:
        return 0
    if any(len(profile) != len(profiles[0]) for profile in profiles):
        raise ValueError("phase class profiles must have a common clock length")
    canonical: list[tuple[int, ...]] = []
    for profile in profiles:
        row_keys = tuple(str(value) for value in profile)
        start = least_cyclic_rotation(
            len(profile),
            row_keys.__getitem__,
            compare=_compare_text,
        )
        canonical.append(profile[start:] + profile[:start])
    return len(set(canonical))


def _compare_text(left: str, right: str) -> int:
    return (left > right) - (left < right)


def _action_profiles(
    states: tuple[BoundaryChart, ...],
    rows: Mapping[BoundaryChart, tuple[ActionCell[BoundaryChart], ...]],
    *,
    include_weights: bool,
) -> tuple[tuple[Hashable, ...], ...]:
    profiles: list[tuple[Hashable, ...]] = []
    for state in states:
        row = rows[state]
        profile = tuple(
            (
                cell.observation,
                tuple(
                    (_stable_value(target), delta)
                    for target, delta in zip(
                        cell.successors, cell.phase_deltas, strict=True
                    )
                ),
                cell.weight if include_weights else (),
            )
            for cell in (row[phase % len(row)] for phase in range(PERIOD))
        )
        profiles.append(profile)
    return tuple(profiles)


def _legacy_control_profile(cell: ActionCell[StateT]) -> Hashable:
    """Diagnostic projection used by earlier 327/294 clock audits.

    It deliberately omits ordered child identities, exact receiving clocks,
    occurrence weights and guard transport. Its classes are not candidate
    semantic IDs; the richer profiles below are the correctness boundary.
    """
    action = cell.observation
    if action[0] == "live":
        return ("live", action[2], None, action[4])
    if action[0] == "fork":
        fork_a = action[1]
        if type(fork_a) is not int:
            raise AssertionError("fork return lost its exact coefficient")
        return ("stop", None, fork_a - 2, 0)
    if action[0] == "landmine":
        return ("stop", None, 8, 0)
    if action[0] == "identity":
        return ("identity",)
    raise AssertionError("completed return has an unexpected output kind")


def _weight_conflicts(
    control: PartitionResult,
    weighted: PartitionResult,
) -> dict[str, object]:
    if control.states != weighted.states:
        raise AssertionError("control and weighted audit state orders differ")
    subclasses: dict[int, set[int]] = {}
    for control_id, weighted_id in zip(
        control.class_ids, weighted.class_ids, strict=True
    ):
        subclasses.setdefault(control_id, set()).add(weighted_id)
    conflicts = {
        class_id: tuple(sorted(weighted_ids))
        for class_id, weighted_ids in subclasses.items()
        if len(weighted_ids) > 1
    }
    return {
        "control_classes_with_distinct_exact_weight_subclasses": len(conflicts),
        "weight_subclasses_by_control_class": conflicts,
        "certified_weight_transport_used": False,
    }


def _build_source_action_report(
    view: SemanticContinuation,
    roots: tuple[BoundaryChart, ...],
) -> dict[str, object]:
    states = tuple(
        sorted(
            view.transitions,
            key=lambda source: (
                source.kind,
                source.leading,
                source.delta,
                source.coordinate,
            ),
        )
    )
    rows = _source_action_rows(view, roots)
    period_counts = Counter(len(rows[state]) for state in states)
    control_rows = tuple(
        tuple(
            (
                cell.observation,
                tuple(
                    (_stable_value(target), phase_delta)
                    for target, phase_delta in zip(
                        cell.successors, cell.phase_deltas, strict=True
                    )
                ),
            )
            for cell in rows[state]
        )
        for state in states
    )
    weighted_rows = tuple(
        tuple(
            (
                cell.observation,
                cell.phase_deltas,
                tuple(
                    (_stable_value(target), phase_delta)
                    for target, phase_delta in zip(
                        cell.successors, cell.phase_deltas, strict=True
                    )
                ),
                cell.weight,
            )
            for cell in rows[state]
        )
        for state in states
    )
    return {
        "scope": "exact SemanticContinuation source states",
        "phase_domain": PERIOD,
        "row_periods": dict(sorted(period_counts.items())),
        "compressed_phase_cells": sum(len(rows[state]) for state in states),
        "phase_aligned_local_action_classes": len(set(control_rows)),
        "phase_aligned_local_weighted_classes": len(set(weighted_rows)),
        "dense_source_by_phase_cells_materialized": False,
        "goto_edges_retained_for_diagnostic": sum(
            cell.observation[0] == "goto" for state in states for cell in rows[state]
        ),
        "source_bindings": tuple(_state_record(state) for state in states),
    }


def _build_completed_b1_report(
    view: SemanticContinuation,
    roots: tuple[BoundaryChart, ...],
) -> dict[str, object]:
    states = tuple(
        sorted(
            view.transitions,
            key=lambda source: (
                source.kind,
                source.leading,
                source.delta,
                source.coordinate,
            ),
        )
    )
    weighted_rows = _completed_source_rows(view, states, roots)
    control_rows = {
        source: tuple(
            ActionCell(cell.observation, cell.successors, cell.phase_deltas)
            for cell in row
        )
        for source, row in weighted_rows.items()
    }
    controls = refine_periodic_action_graph(
        states, control_rows, include_weights=False, clock_period=PERIOD
    )
    weighted = refine_periodic_action_graph(
        states, weighted_rows, include_weights=True, clock_period=PERIOD
    )
    exact_control_profiles = _action_profiles(
        states, control_rows, include_weights=False
    )
    exact_weighted_profiles = _action_profiles(
        states, weighted_rows, include_weights=True
    )
    legacy_profiles = tuple(
        tuple(_legacy_control_profile(row[phase % len(row)]) for phase in range(PERIOD))
        for row in (control_rows[source] for source in states)
    )
    state_indices = {source: index for index, source in enumerate(states)}
    root_indices = tuple(state_indices[root] for root in roots)

    def root_class_count(class_ids: tuple[int, ...]) -> int:
        return len({class_ids[index] for index in root_indices})

    return {
        "scope": (
            "completed exact B1 result for every source continuation; internal "
            "Goto is resolved, Live root edges are successor-closed, and Fork "
            "retains its ordered exact child recipes as terminal observations"
        ),
        "phase_domain": PERIOD,
        "source_state_count": len(states),
        "root_count": len(roots),
        "compressed_completed_action_slots": sum(
            len(weighted_rows[source]) for source in states
        ),
        "maximum_completed_local_period": max(
            len(weighted_rows[source]) for source in states
        ),
        "dense_completed_action_rows_retained": False,
        "control_return_function_equivalence": _profile_partitions(
            exact_control_profiles
        ),
        "full_physical_action_weighted_return_function_equivalence": _profile_partitions(
            exact_weighted_profiles
        ),
        "control_completed_action_right_congruence": _partition_summary(controls),
        "full_physical_action_weighted_completed_action_right_congruence": (
            _partition_summary(weighted)
        ),
        "canonical_46_root_projection": {
            "root_sources": tuple(_state_record(root) for root in roots),
            "control_completed_action_classes": root_class_count(controls.class_ids),
            "weighted_completed_action_classes": root_class_count(weighted.class_ids),
        },
        "historical_coarse_control_projection": _profile_partitions(legacy_profiles),
        "historical_projection_scope": (
            "kind, canonical Live fiber, exact Stop J, exponent advance only; "
            "omits ordered child identities, phase transport details, guards "
            "and occurrence weights, and cannot serve as a semantic ID"
        ),
        "weight_conflicts": _weight_conflicts(controls, weighted),
        "source_to_root_binding": tuple(
            {
                "source": _state_record(source),
                "fiber": offset_orbit(source.coordinate),
            }
            for source in roots
        ),
        "note": (
            "All source continuations are completed through internal Goto "
            "actions. Live returns point to exact admitted root charts with "
            "the +1 receiving-phase transport. Fork returns retain ordered "
            "N/Z successor recipes and their exact phase displacement. "
            "Landmine has no successors. Physical path fragments remain a "
            "separate weighted diagnostic."
        ),
    }


def build_right_congruence_report() -> dict[str, object]:
    """Build the bounded exact audit using current source constructors."""
    roots = canonical_roots()
    view = production_semantic_owner(roots)
    action_count = sum(len(row) for row in view.transitions.values())
    source_action = _build_source_action_report(view, roots)
    completed_b1 = _build_completed_b1_report(view, roots)
    return {
        "format": "comma-b1-right-congruence-audit-v1",
        "authority": "exact executable source/chart constructors",
        "source_root_count": len(roots),
        "source_action_state_count": len(view.transitions),
        "source_action_slot_count": action_count,
        "source_action_graph": source_action,
        "completed_b1": completed_b1,
        "phase_rebase": (
            "phase-aligned classes retain source bindings; common translation "
            "is reported separately as occurrence data"
        ),
        "common_phase_translation": (
            "reported separately for complete-return profiles and not erased "
            "from source bindings or production cache identities"
        ),
        "production_cutover": False,
        "rank_or_terminal_candidate_oracle": False,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        help="write exact audit JSON to a file instead of standard output",
    )
    arguments = parser.parse_args(argv)
    report = build_right_congruence_report()
    encoded = json.dumps(report, sort_keys=True, separators=(",", ":")) + "\n"
    if arguments.output:
        with open(arguments.output, "w", encoding="utf-8") as output:
            output.write(encoded)
    else:
        print(encoded, end="")
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
