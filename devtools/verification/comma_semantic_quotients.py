"""Explicit finite audits of comma-port and future Moore quotients.

This research module is not installed with the runtime package. Functions build
their finite tables only when called. A quotient observes finite control; it
does not contain exact radial displacement, dwell, guard, or source occurrence
data and cannot authorize a weighted transfer or an infinite branch.
"""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.functions.finite_observer import (
    FiniteObserverMinimization,
    class_members,
    map_partition_row,
    minimize_finite_observer,
    partition_quotient_rows,
)
from number_compiler.sequences.comma.arithmetic import (
    comma_port_next,
    comma_port_previous,
    cycle_transfer,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD, chart_moves
from number_compiler.sequences.comma.boundary_quotient import BoundaryState
from number_compiler.sequences.comma.cycle_spatial import CycleSpatialState

BranchSymbol = Literal[0, 1]
_BRANCH_SLOT: dict[BranchSymbol, int] = {0: 1, 1: 0}


@dataclass(frozen=True, slots=True)
class CommaPortMooreQuotient:
    """A fixed-point Moore partition of the declared comma-port alphabet."""

    ports: tuple[tuple[int, int], ...]
    class_ids: tuple[int, ...]
    transitions: tuple[int, ...]
    outputs: tuple[Hashable, ...]
    classes: int
    fixed_classes: int
    rounds: int

    def class_for_port(self, leading: int, digit: int) -> int:
        if (
            type(leading) is not int
            or not 1 <= leading <= 9
            or type(digit) is not int
            or not 0 <= digit <= 9
        ):
            raise ValueError("invalid comma port")
        try:
            index = self.ports.index((leading, digit))
        except ValueError as exc:
            raise ValueError("comma port lies outside this Moore alphabet") from exc
        return self.class_ids[index]


def _build_port_quotient(*, include_zero: bool) -> CommaPortMooreQuotient:
    digits = range(10) if include_zero else range(1, 10)
    ports = tuple((leading, digit) for leading in range(1, 10) for digit in digits)
    indices = {port: index for index, port in enumerate(ports)}
    transitions = tuple(indices[(port[0], comma_port_next(*port))] for port in ports)
    if include_zero:
        # Keep the short temporal period and physical-zero event observable.
        # Absolute dwell and radial displacement remain occurrence payload.
        outputs: tuple[Hashable, ...] = tuple(
            (comma_port_previous(*port) == 0, cycle_transfer(*port).period)
            for port in ports
        )
        expected = 19
    else:
        outputs = tuple(comma_port_previous(*port) == 0 for port in ports)
        expected = 15
    minimized = minimize_finite_observer(
        tuple((target,) for target in transitions), outputs
    )
    if minimized.classes != expected:
        raise AssertionError(
            f"comma port quotient closed at {minimized.classes}, expected {expected}"
        )

    members = class_members(minimized.class_ids, minimized.classes)
    quotient_rows: list[tuple[int, ...]] = []
    quotient_outputs: list[Hashable] = []
    for member_group in members:
        representative = member_group[0]
        target_class = map_partition_row(
            (transitions[representative],), minimized.class_ids
        )[0]
        if target_class is None:
            raise AssertionError("comma port transition was forbidden")
        output = outputs[representative]
        for state in member_group[1:]:
            other_target = map_partition_row(
                (transitions[state],), minimized.class_ids
            )[0]
            if other_target != target_class:
                raise AssertionError("comma port class is not successor closed")
            if outputs[state] != output:
                raise AssertionError("comma port class merged distinct observations")
        quotient_rows.append((target_class,))
        quotient_outputs.append(output)
    fixed = minimize_finite_observer(tuple(quotient_rows), tuple(quotient_outputs))
    if fixed.classes != minimized.classes:
        raise AssertionError("comma port quotient is not a Moore fixed point")
    return CommaPortMooreQuotient(
        ports,
        minimized.class_ids,
        transitions,
        outputs,
        minimized.classes,
        fixed.classes,
        minimized.rounds,
    )


def build_q15_nonzero_ports() -> CommaPortMooreQuotient:
    """Build the 81-port nonzero observer (15 stable classes)."""
    return _build_port_quotient(include_zero=False)


def build_q19_production_ports() -> CommaPortMooreQuotient:
    """Build the 90-port zero-inclusive production observer (19 classes)."""
    return _build_port_quotient(include_zero=True)


def boundary_production_port(state: BoundaryState) -> tuple[int, int]:
    """Return the decimal production port at a fork-boundary occurrence.

    ``N(a,p) = a*10**p - 1`` ends in ``(a-1, 9)``; ``Z(a,p)`` ends in
    ``(a, 0)``. Exact weights and guards remain attached to the occurrence.
    """
    if type(state) is not BoundaryState:
        raise ValueError("comma boundary observation requires a BoundaryState")
    return (state.a - 1, 9) if state.kind == "N" else (state.a, 0)


@dataclass(frozen=True, slots=True)
class CommaFutureGraph:
    states: tuple[BoundaryState, ...]
    transitions: tuple[tuple[int | None, int | None], ...]
    exponent_deltas: tuple[int, ...]


def build_future_graph() -> CommaFutureGraph:
    """Build the 14,784-state exact future graph from NC5 chart arithmetic."""
    states = tuple(
        BoundaryState(kind, a, residue)
        for kind in ("N", "Z")
        for a in range(2, 10)
        for residue in range(PERIOD)
    )
    index = {state: state_id for state_id, state in enumerate(states)}
    transitions: list[tuple[int | None, int | None]] = []
    exponent_deltas: list[int] = []
    for state in states:
        for chart, move in chart_moves(
            state.kind, state.a, state.exponent_residue, grouped_near=True
        ):
            if move.next_chart is not None:
                continue
            exponent_deltas.append(chart.delta)
            if move.fork_a is None:
                transitions.append((None, None))
            else:
                phase = (state.exponent_residue + chart.delta) % PERIOD
                transitions.append(
                    (
                        index[BoundaryState("N", move.fork_a, phase)],
                        index[BoundaryState("Z", move.fork_a, phase)],
                    )
                )
            break
        else:
            raise AssertionError("comma chart failed to reach a terminal boundary")
    if len(states) != 14_784 or len(transitions) != len(states):
        raise AssertionError("comma future universe is incomplete")
    return CommaFutureGraph(states, tuple(transitions), tuple(exponent_deltas))


def _quotient_rows(
    raw_rows: tuple[tuple[int | None, int | None], ...],
    minimization: FiniteObserverMinimization,
    outputs: tuple[Hashable, ...],
) -> tuple[tuple[tuple[int | None, int | None], ...], tuple[Hashable, ...]]:
    members = class_members(minimization.class_ids, minimization.classes)
    quotient_rows = partition_quotient_rows(
        raw_rows, minimization.class_ids, minimization.classes
    )
    rows: list[tuple[int | None, int | None]] = []
    class_outputs: list[Hashable] = []
    for group, row in zip(members, quotient_rows, strict=True):
        representative = group[0]
        row_values = row
        if len(row_values) != 2:
            raise AssertionError("comma future row lost its ordered fork slots")
        row_pair = (row_values[0], row_values[1])
        output = outputs[representative]
        for state in group[1:]:
            if outputs[state] != output:
                raise AssertionError("comma future class merged distinct observations")
        rows.append(row_pair)
        class_outputs.append(output)
    return tuple(rows), tuple(class_outputs)


@dataclass(frozen=True, slots=True)
class CommaFutureMooreQuotient:
    raw_states: int
    classes: int
    fixed_classes: int
    class_ids: tuple[int, ...]
    transitions: tuple[tuple[int | None, int | None], ...]
    outputs: tuple[Hashable, ...]
    rounds: int

    def class_for_state(self, state: BoundaryState, graph: CommaFutureGraph) -> int:
        try:
            raw_id = graph.states.index(state)
        except ValueError as exc:
            raise ValueError(
                "boundary state lies outside comma future universe"
            ) from exc
        return self.class_ids[raw_id]


def _minimize_future(
    graph: CommaFutureGraph, outputs: tuple[Hashable, ...], expected: int
) -> CommaFutureMooreQuotient:
    minimized = minimize_finite_observer(graph.transitions, outputs)
    if minimized.classes != expected:
        raise AssertionError(
            f"comma future quotient closed at {minimized.classes}, expected {expected}"
        )
    rows, class_outputs = _quotient_rows(graph.transitions, minimized, outputs)
    fixed = minimize_finite_observer(rows, class_outputs)
    if fixed.classes != minimized.classes:
        raise AssertionError("comma future quotient is not a Moore fixed point")
    return CommaFutureMooreQuotient(
        len(graph.states),
        minimized.classes,
        fixed.classes,
        minimized.class_ids,
        rows,
        class_outputs,
        minimized.rounds,
    )


def build_future_temporal_quotient(
    graph: CommaFutureGraph,
) -> CommaFutureMooreQuotient:
    """Build the coarsest exact zero-aware future right congruence (T3279)."""
    return _minimize_future(graph, tuple(0 for _ in graph.states), 3_279)


def build_future_production_macro_quotient(
    graph: CommaFutureGraph,
) -> CommaFutureMooreQuotient:
    """Build T3279 refined by the closed, zero-inclusive Q19 observation."""
    outputs = tuple(
        CycleSpatialState.from_port(*boundary_production_port(state))
        for state in graph.states
    )
    return _minimize_future(graph, outputs, 4_986)


@dataclass(frozen=True, slots=True)
class CommaFutureRankAudit:
    losing_states: int
    survivor_states: int
    maximum_rank: int
    temporal_classes: int
    mixed_rank_classes: int
    cycle_length: int
    cycle_exponent_gain: int
    zero_symbols: int
    one_symbols: int
    cyclic_runs: int
    all_five_bit_words: bool


def future_losing_ranks(graph: CommaFutureGraph) -> tuple[int | None, ...]:
    """Compute the least finite losing ranks; unranked is not a runtime authority."""
    rank: list[int | None] = [
        0 if row == (None, None) else None for row in graph.transitions
    ]
    while True:
        newly: dict[int, int] = {}
        for state, row in enumerate(graph.transitions):
            if rank[state] is not None or row == (None, None):
                continue
            child_ranks = tuple(rank[target] for target in row if target is not None)
            if len(child_ranks) == 2 and all(
                value is not None for value in child_ranks
            ):
                known = [value for value in child_ranks if value is not None]
                newly[state] = 1 + max(known)
        if not newly:
            break
        for state, value in newly.items():
            rank[state] = value

    return tuple(rank)


def future_rank_refinement_audit(
    graph: CommaFutureGraph, quotient: CommaFutureMooreQuotient
) -> CommaFutureRankAudit:
    """Audit termination ranks after independently constructing T3279."""
    rank = future_losing_ranks(graph)

    members = class_members(quotient.class_ids, quotient.classes)
    mixed = sum(1 for group in members if len({rank[state] for state in group}) != 1)
    if mixed:
        raise AssertionError("comma future Moore class mixes termination ranks")
    losing_ranks = [value for value in rank if value is not None]
    winning = {state for state, value in enumerate(rank) if value is None}
    start = graph.states.index(BoundaryState("N", 2, 10))
    cursor = start
    visited: dict[int, int] = {}
    logical_symbols: list[int] = []
    exponent_gain = 0
    while cursor not in visited:
        visited[cursor] = len(visited)
        row = graph.transitions[cursor]
        live = [
            (slot, target)
            for slot, target in enumerate(row)
            if target is not None and target in winning
        ]
        if len(live) != 1:
            raise AssertionError("comma survivor graph is not uniquely continuing")
        slot, target = live[0]
        logical_symbols.append(0 if slot == 1 else 1)
        exponent_gain += graph.exponent_deltas[cursor]
        cursor = target
    if cursor != start or len(visited) != len(winning):
        raise AssertionError("comma survivors do not form the checked root cycle")
    cyclic_runs = sum(
        logical_symbols[index] != logical_symbols[index - 1]
        for index in range(len(logical_symbols))
    )
    windows = {
        tuple(
            logical_symbols[(index + offset) % len(logical_symbols)]
            for offset in range(5)
        )
        for index in range(len(logical_symbols))
    }
    if not losing_ranks:
        raise AssertionError("comma future graph has no losing states")
    return CommaFutureRankAudit(
        losing_states=len(losing_ranks),
        survivor_states=len(winning),
        maximum_rank=max(losing_ranks),
        temporal_classes=quotient.classes,
        mixed_rank_classes=mixed,
        cycle_length=len(visited),
        cycle_exponent_gain=exponent_gain,
        zero_symbols=logical_symbols.count(0),
        one_symbols=logical_symbols.count(1),
        cyclic_runs=cyclic_runs,
        all_five_bit_words=len(windows) == 32,
    )


@dataclass(frozen=True, slots=True)
class CommaHomogeneousRunAudit:
    actions: int
    zero_saturates_at: int
    one_saturates_at: int
    common_dead_action: bool


def _compose_transform(
    left: tuple[int, ...], right: tuple[int, ...]
) -> tuple[int, ...]:
    return tuple(right[left[state]] for state in range(len(left)))


def future_homogeneous_run_audit(
    quotient: CommaFutureMooreQuotient,
) -> CommaHomogeneousRunAudit:
    """Compute homogeneous logical 0/1 actions extensionally on T3279."""
    dead = quotient.classes
    total_rows = tuple(
        tuple(dead if target is None else target for target in row)
        for row in quotient.transitions
    )
    generators: dict[BranchSymbol, tuple[int, ...]] = {
        symbol: tuple(row[_BRANCH_SLOT[symbol]] for row in total_rows) + (dead,)
        for symbol in (0, 1)
    }
    identity = tuple(range(dead + 1))
    dead_action = tuple(dead for _ in range(dead + 1))
    saturation: dict[BranchSymbol, int] = {}
    actions = {identity}
    for symbol in (0, 1):
        action = identity
        for exponent in range(1, 64):
            action = _compose_transform(action, generators[symbol])
            actions.add(action)
            if action == dead_action:
                saturation[symbol] = exponent
                break
        else:
            raise AssertionError("comma homogeneous run did not saturate")
    if saturation != {0: 13, 1: 18}:
        raise AssertionError(f"unexpected comma run saturation {saturation}")
    if len(actions) != 31:
        raise AssertionError(
            f"comma homogeneous powers have {len(actions)} actions, expected 31"
        )
    return CommaHomogeneousRunAudit(31, 13, 18, dead_action in actions)


__all__ = [
    "CommaFutureGraph",
    "CommaFutureMooreQuotient",
    "CommaFutureRankAudit",
    "CommaHomogeneousRunAudit",
    "CommaPortMooreQuotient",
    "boundary_production_port",
    "build_future_graph",
    "build_future_production_macro_quotient",
    "build_future_temporal_quotient",
    "build_q15_nonzero_ports",
    "build_q19_production_ports",
    "future_homogeneous_run_audit",
    "future_losing_ranks",
    "future_rank_refinement_audit",
]
