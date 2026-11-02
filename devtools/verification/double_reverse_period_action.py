"""Conditional effective-seam actions for exact 2rev10 birth-ring states."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Literal

from devtools.verification.double_reverse_period_source import (
    MAX_DEPTH,
    MAX_GENERATION,
    MAX_RETAINED_ROW_BYTES,
    MAX_SAMPLED_ROWS,
    MAX_WINDOW,
    SourceEvidenceRefused,
    SpatialReturnRow,
    effective_gate,
)
from number_compiler.arithmetic.automata.word_period import primitive_period
from number_compiler.sequences.double_reverse.boundary_cycles import (
    CANDIDATE_COMPONENTS,
)
from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell
from number_compiler.sequences.double_reverse.temporal_birth_ring import (
    BirthRingPorts,
    BirthRingState,
)
from number_compiler.sequences.double_reverse.temporal_diagonal_induction import (
    SeamGate,
    seam_gate,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_borders import (
    edge_phase,
    growth_ports,
)

MAX_ACTION_STATES = 8_192


class ConditionalActionRefused(ValueError):
    """A declared effective-seam transition is outside its exact domain."""


class ConditionalActionBudgetExceeded(ValueError):
    pass


@dataclass(frozen=True, slots=True)
class ConditionalActionRefusalReport:
    status: Literal[
        "conditional_action_refused",
        "conditional_action_budget_exceeded",
        "source_rows_incomplete",
        "source_guard_mismatch",
    ]
    scope: str
    detail: str


@dataclass(frozen=True, slots=True)
class ConditionalActionLasso:
    gate_program_fsteps: int
    preperiod_fsteps: int
    state_period_fsteps: int
    bank_output_period_fsteps: int
    states_examined: int
    period_comparisons: int


@dataclass(frozen=True, slots=True)
class SourceActionObservation:
    physical_generation: int
    state: BirthRingState
    gate: SeamGate


@dataclass(frozen=True, slots=True)
class SourceGuardCheck:
    status: Literal["matched_requested_rows", "first_mismatch", "missing_rows"]
    checked_fsteps: int
    first_mismatch_fstep: int | None
    mismatch_kind: str | None
    mismatch_generation: int | None
    checked_through_physical_generation: int | None


@dataclass(frozen=True, slots=True)
class ConditionalActionReport:
    status: Literal[
        "closed_conditional_action", "source_guard_mismatch", "source_rows_incomplete"
    ]
    scope: str
    gate_program: tuple[SeamGate, ...]
    lasso: ConditionalActionLasso
    power_fsteps: int
    powered_state: BirthRingState
    source_guard: SourceGuardCheck


@dataclass(frozen=True, slots=True)
class _ConditionalModel:
    states: tuple[BirthRingState, ...]
    lasso: ConditionalActionLasso

    def at(self, fsteps: int) -> BirthRingState:
        if type(fsteps) is not int or fsteps < 0:
            raise ValueError("conditional action exponent must be nonnegative")
        if fsteps < len(self.states):
            return self.states[fsteps]
        lasso = self.lasso
        return self.states[
            lasso.preperiod_fsteps
            + (fsteps - lasso.preperiod_fsteps) % lasso.state_period_fsteps
        ]


def _representative_inlet(state: BirthRingState, gate: SeamGate) -> BirthRingPorts:
    if gate.phase != state.phase:
        raise ConditionalActionRefused("gate phase does not match bank phase")
    left_birth, right_birth = growth_ports(state.phase, 1)
    if (gate.left_output is None) != bool(left_birth):
        raise ConditionalActionRefused("left gate contradicts source growth port")
    if (gate.right_output is None) != bool(right_birth):
        raise ConditionalActionRefused("right gate contradicts source growth port")

    def left_witness() -> int:
        if left_birth:
            return 0
        previous = state.left[-2] if state.pairs > 1 else 0
        center = state.left[-1]
        return next(
            (
                digit
                for digit in range(10)
                if stencil_cell(previous, center, digit) == gate.left_output
            ),
            -1,
        )

    def right_witness() -> int:
        if right_birth:
            return 0
        following = state.right[1] if state.pairs > 1 else 0
        center = state.right[0]
        return next(
            (
                digit
                for digit in range(10)
                if stencil_cell(digit, center, following) == gate.right_output
            ),
            -1,
        )

    left, right = left_witness(), right_witness()
    if left < 0 or right < 0:
        raise ConditionalActionRefused("effective gate has no decimal inlet witness")
    inlet = BirthRingPorts(left, right)
    if seam_gate(state, inlet) != gate:
        raise AssertionError("representative inlet failed exact seam-gate check")
    return inlet


def _in_closed_border_cylinder(state: BirthRingState) -> bool:
    if state.pairs < 2:
        return True
    upper = (state.left[0], state.left[1])
    lower = (state.right[-2], state.right[-1])
    edge = (*upper, *lower)
    return edge_phase(upper, lower) == state.phase and edge in CANDIDATE_COMPONENTS[0]


def _advance_effective_gate(state: BirthRingState, gate: SeamGate) -> BirthRingState:
    if not _in_closed_border_cylinder(state):
        raise ConditionalActionRefused("bank left the source-closed outer cylinder")
    next_state = state.advance(_representative_inlet(state, gate))[0]
    if not _in_closed_border_cylinder(next_state):
        raise ConditionalActionRefused(
            "effective seam exits the source-closed border SCC"
        )
    return next_state


def close_effective_program(
    initial: BirthRingState,
    program: tuple[SeamGate, ...],
    *,
    max_states: int,
) -> _ConditionalModel:
    """Close the exact ``(bank, program index)`` transition-semigroup orbit."""
    if (
        type(initial) is not BirthRingState
        or type(program) is not tuple
        or not program
        or any(type(gate) is not SeamGate for gate in program)
        or type(max_states) is not int
        or not 1 <= max_states <= MAX_ACTION_STATES
        or len(program) > max_states
    ):
        raise ValueError("invalid conditional gate-program request")
    estimate = max_states * (256 + 80 * initial.pairs) + 128 * len(program)
    if estimate > MAX_RETAINED_ROW_BYTES:
        raise ConditionalActionBudgetExceeded("conditional action exceeds memory cap")
    states: list[BirthRingState] = []
    seen: dict[tuple[BirthRingState, int], int] = {}
    current = initial
    step = 0
    while True:
        program_index = step % len(program)
        key = (current, program_index)
        prior = seen.get(key)
        if prior is not None:
            cycle = states[prior:step]
            bank_period, period_comparisons = primitive_period(
                tuple((state.left, state.right) for state in cycle)
            )
            return _ConditionalModel(
                tuple(states),
                ConditionalActionLasso(
                    len(program),
                    prior,
                    step - prior,
                    bank_period,
                    step,
                    period_comparisons,
                ),
            )
        if step >= max_states:
            raise ConditionalActionBudgetExceeded(
                "declared conditional seam action did not close within its state budget"
            )
        seen[key] = step
        states.append(current)
        try:
            current = _advance_effective_gate(current, program[program_index])
        except ConditionalActionRefused as error:
            raise ConditionalActionRefused(
                f"conditional seam action refuses at F-step {step}: {error}"
            ) from error
        step += 1


def _source_state(row: SpatialReturnRow, depth: int) -> BirthRingState:
    if type(depth) is not int or not 1 <= depth < len(row.left):
        raise ValueError("source bank depth exceeds retained edge strip")
    return BirthRingState(
        tuple(int(digit) for digit in row.left[:depth]),
        tuple(int(digit) for digit in row.right[-depth:]),
        row.phase,
    )


def _verify_source_action(
    rows: dict[int, SpatialReturnRow],
    *,
    anchor: int,
    depth: int,
    physical_period: int,
    window: int,
    program: tuple[SeamGate, ...],
    model: _ConditionalModel,
) -> SourceGuardCheck:
    observations: list[SourceActionObservation] = []
    for fstep in range((window + 1) // 2):
        generation = anchor + physical_period + 2 * fstep
        row = rows.get(generation)
        if row is None:
            return SourceGuardCheck(
                "missing_rows",
                len(observations),
                None,
                "source_row_missing",
                generation,
                observations[-1].physical_generation if observations else None,
            )
        observations.append(
            SourceActionObservation(
                generation, _source_state(row, depth), effective_gate(row, depth)
            )
        )
    return check_source_action_block(
        observations,
        program=program,
        model=model,
        model_offset=len(program),
    )


def check_source_action_block(
    observations: Sequence[SourceActionObservation],
    *,
    program: tuple[SeamGate, ...],
    model: _ConditionalModel,
    model_offset: int,
) -> SourceGuardCheck:
    """Check exact observed gate/bank rows against one conditional block."""
    if not program:
        raise ValueError("conditional source-action program must be nonempty")
    if type(model_offset) is not int or model_offset < 0:
        raise ValueError("conditional source-action offset must be nonnegative")
    if not observations:
        return SourceGuardCheck("missing_rows", 0, None, "no_observations", None, None)
    checked = 0
    for fstep, observation in enumerate(observations):
        if observation.gate != program[(model_offset + fstep) % len(program)]:
            return SourceGuardCheck(
                "first_mismatch",
                checked,
                fstep,
                "effective_gate",
                observation.physical_generation,
                observations[checked - 1].physical_generation if checked else None,
            )
        if observation.state != model.at(model_offset + fstep):
            return SourceGuardCheck(
                "first_mismatch",
                checked,
                fstep,
                "bank_state",
                observation.physical_generation,
                observations[checked - 1].physical_generation if checked else None,
            )
        checked += 1
    last_generation = observations[-1].physical_generation if observations else None
    return SourceGuardCheck(
        "matched_requested_rows", checked, None, None, None, last_generation
    )


def conditional_action(
    rows: dict[int, SpatialReturnRow],
    *,
    anchor: int,
    depth: int,
    physical_period: int,
    window: int,
    power_fsteps: int,
    max_states: int,
) -> ConditionalActionReport:
    """Power a declared source gate block and separately check its next block."""
    if (
        type(rows) is not dict
        or type(anchor) is not int
        or anchor < 0
        or type(depth) is not int
        or not 1 <= depth <= MAX_DEPTH
        or type(physical_period) is not int
        or not 4 <= physical_period <= MAX_GENERATION
        or physical_period % 4
        or type(window) is not int
        or not 1 <= window <= MAX_WINDOW
        or type(power_fsteps) is not int
        or power_fsteps < 0
        or type(max_states) is not int
        or not 1 <= max_states <= MAX_ACTION_STATES
    ):
        raise ValueError("invalid bounded conditional-action request")
    program_length = physical_period // 2
    if program_length > MAX_SAMPLED_ROWS or len(rows) > MAX_SAMPLED_ROWS:
        raise ConditionalActionBudgetExceeded(
            "conditional action exceeds the sampled-row budget"
        )
    program_rows = tuple(rows.get(anchor + 2 * step) for step in range(program_length))
    if any(row is None for row in program_rows):
        raise SourceEvidenceRefused("not all source rows for the gate program exist")
    typed_rows = tuple(row for row in program_rows if row is not None)
    initial = _source_state(typed_rows[0], depth)
    gates = tuple(effective_gate(row, depth) for row in typed_rows)
    model = close_effective_program(initial, gates, max_states=max_states)
    for fstep, row in enumerate(typed_rows):
        if _source_state(row, depth) != model.at(fstep):
            guard = SourceGuardCheck(
                "first_mismatch",
                fstep,
                fstep,
                "first_block_state",
                row.generation,
                typed_rows[fstep - 1].generation if fstep else None,
            )
            return ConditionalActionReport(
                "source_guard_mismatch",
                "conditional on the declared effective-seam gate program",
                gates,
                model.lasso,
                power_fsteps,
                model.at(power_fsteps),
                guard,
            )
    guard = _verify_source_action(
        rows,
        anchor=anchor,
        depth=depth,
        physical_period=physical_period,
        window=window,
        program=gates,
        model=model,
    )
    status: Literal[
        "closed_conditional_action", "source_guard_mismatch", "source_rows_incomplete"
    ]
    if guard.status == "matched_requested_rows":
        status = "closed_conditional_action"
    elif guard.status == "first_mismatch":
        status = "source_guard_mismatch"
    else:
        status = "source_rows_incomplete"
    return ConditionalActionReport(
        status,
        "conditional on the declared effective-seam gate program",
        gates,
        model.lasso,
        power_fsteps,
        model.at(power_fsteps),
        guard,
    )
