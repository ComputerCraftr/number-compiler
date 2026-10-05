"""Complete-domain B1 key sufficiency audit, never a production constructor.

The chart arithmetic is an explicit reference teacher. Source-local projections
are dominated by the exact C1 suffix; adding more functions of that suffix
cannot separate a collision. No endpoint, observation or raw phase is put into
a candidate key. All-core residues are an exact baseline, not a claimed small
quotient. Port-move time and decimal-exponent phase are not interchangeable.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import Literal

from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
)
from number_compiler.sequences.comma.arithmetic import (
    cycle_power_residue,
    cycle_transfer,
)
from number_compiler.sequences.comma.boundary_chart import (
    PERIOD,
    BoundaryChart,
    chart_step,
)
from number_compiler.sequences.comma.carry_generator import C1Phase


@dataclass(frozen=True)
class B1State:
    fiber: int
    phase: int


@dataclass(frozen=True)
class B1Observation:
    """The B1 word projection, not the full public decade-control payload."""

    kind: Literal["live", "fork", "landmine"]
    value: int


@dataclass(frozen=True)
class B1Reference:
    observation: B1Observation
    successor: B1State | None
    chart_visits: int


def offset_orbit(offset: int) -> int:
    """The checked HOL comma_offset_orbit, with signed subtraction."""
    digit = offset % 10
    return (offset - (5 * digit**2 - 4 * digit)) % 460 // 10


def offset_representatives() -> tuple[int, ...]:
    representatives: dict[int, int] = {}
    for offset in range(91):
        representatives.setdefault(offset_orbit(offset), offset)
    if set(representatives) != set(range(46)):
        raise AssertionError("canonical decade offsets do not cover 46 fibers")
    return tuple(representatives[fiber] for fiber in range(46))


def chart_measure(chart: BoundaryChart) -> tuple[int, int, int]:
    """Return the decreasing measure shared by bounded B1 chart walkers."""
    return 10 - chart.leading, int(chart.kind == "entry"), chart.coordinate


def observe_b1(state: B1State) -> B1Reference:
    """Existing chart reference: stop at the first decade seam or terminal.

    Termination follows the decreasing sector/Entry/Near measure. This does not
    call the response-row interpreter or a future/rank/forest evaluator.
    """
    if (
        type(state.fiber) is not int
        or not 0 <= state.fiber < 46
        or type(state.phase) is not int
        or not 0 <= state.phase < PERIOD
    ):
        raise ValueError("B1 requires a canonical fiber and phase")
    return _observe_chart(state, offset_representatives()[state.fiber])


def _observe_chart(state: B1State, offset: int) -> B1Reference:
    chart = BoundaryChart("entry", 1, 0, offset)
    visits = 0
    while True:
        move = chart_step(state.phase, chart)
        visits += 1
        target = move.next_chart
        if target is None:
            observation = (
                B1Observation("landmine", 0)
                if move.fork_a is None
                else B1Observation("fork", move.fork_a)
            )
            return B1Reference(observation, None, visits)
        if target.delta != 0:
            if (target.kind, target.leading, target.delta) != ("entry", 1, 1):
                raise AssertionError("B1 crossing changed its decade transport")
            successor = B1State(
                offset_orbit(target.coordinate), (state.phase + 1) % PERIOD
            )
            return B1Reference(
                B1Observation("live", successor.fiber), successor, visits
            )
        if not chart_measure(target) < chart_measure(chart):
            raise AssertionError("B1 chart reference failed its decreasing measure")
        chart = target


@dataclass(frozen=True)
class KeyConflict:
    left: B1State
    right: B1State
    left_observation: B1Observation
    right_observation: B1Observation
    differing_core_modulus: int | None


@dataclass(frozen=True)
class CandidateAudit:
    name: str
    classes: int
    observation_conflicts: int
    successor_conflicts: int
    first_conflict: KeyConflict | None


def _candidate_audit(
    name: str,
    states: tuple[B1State, ...],
    observations: tuple[B1Reference, ...],
    keys: tuple[tuple[int, ...], ...],
    moduli: tuple[int, ...],
    residues: tuple[tuple[int, ...], ...],
) -> CandidateAudit:
    retained: dict[tuple[int, ...], int] = {}
    observation_conflicts = successor_conflicts = 0
    first = None
    for index, (state, reference, key) in enumerate(
        zip(states, observations, keys, strict=True)
    ):
        previous = retained.setdefault(key, index)
        earlier = observations[previous]
        observation_differs = reference.observation != earlier.observation
        left_key = (
            None
            if earlier.successor is None
            else keys[earlier.successor.fiber * PERIOD + earlier.successor.phase]
        )
        right_key = (
            None
            if reference.successor is None
            else keys[reference.successor.fiber * PERIOD + reference.successor.phase]
        )
        observation_conflicts += observation_differs
        successor_conflicts += left_key != right_key
        if first is None and (observation_differs or left_key != right_key):
            other = states[previous]
            separating = next(
                (
                    modulus
                    for modulus, left, right in zip(
                        moduli,
                        residues[other.phase],
                        residues[state.phase],
                        strict=True,
                    )
                    if left != right
                ),
                None,
            )
            first = KeyConflict(
                other, state, earlier.observation, reference.observation, separating
            )
    return CandidateAudit(
        name, len(retained), observation_conflicts, successor_conflicts, first
    )


def _key_rows(
    local: tuple[C1Phase, ...],
    states: tuple[B1State, ...],
    residues: tuple[tuple[int, ...], ...],
    selected: tuple[int, ...],
) -> tuple[tuple[int, ...], ...]:
    return tuple(
        (local[state.fiber].mod4, local[state.fiber].mod25)
        + tuple(residues[state.phase][index] for index in selected)
        for state in states
    )


def audit_b1_quotient(*, expanded_moore_baseline: bool = False) -> dict[str, object]:
    """Audit all 46*924 states; the API intentionally has no partial-pass mode."""
    representatives = offset_representatives()
    local = tuple(C1Phase.from_suffix(1, value) for value in representatives)
    moduli = tuple(
        sorted(
            {cycle_transfer(f, d).displacement for f in range(1, 10) for d in range(10)}
        )
    )
    residues = tuple(
        tuple(cycle_power_residue(modulus, phase) for modulus in moduli)
        for phase in range(PERIOD)
    )
    states = tuple(
        B1State(fiber, phase) for fiber in range(46) for phase in range(PERIOD)
    )
    observations = tuple(
        _observe_chart(state, representatives[state.fiber]) for state in states
    )
    source_index = moduli.index(460)
    candidates = []
    for name, selected in (
        ("source_local", ()),
        ("source_core_460", (source_index,)),
        ("all_core_residues", tuple(range(len(moduli)))),
    ):
        keys = _key_rows(local, states, residues, selected)
        candidates.append(
            _candidate_audit(name, states, observations, keys, moduli, residues)
        )
    selected = (source_index,)
    refinement = []
    while True:
        keys = _key_rows(local, states, residues, selected)
        candidate = _candidate_audit(
            "core_refinement", states, observations, keys, moduli, residues
        )
        refinement.append(
            {"moduli": tuple(moduli[i] for i in selected), **asdict(candidate)}
        )
        if candidate.first_conflict is None:
            break
        separator = candidate.first_conflict.differing_core_modulus
        if separator is None or moduli.index(separator) in selected:
            raise AssertionError("core refinement has no new separating coordinate")
        selected += (moduli.index(separator),)
    # The expanded graph is a historical differential baseline, never the
    # source classifier. Do not repeatedly minimize it for a key audit.
    moore = None
    if expanded_moore_baseline:
        moore = minimize_finite_observer(
            tuple(
                (
                    None
                    if row.successor is None
                    else row.successor.fiber * PERIOD + row.successor.phase,
                )
                for row in observations
            ),
            tuple(row.observation for row in observations),
        )
    return {
        "scope": "finite key sufficiency only; chart teacher is not a replacement B1 producer",
        "observation": "Comma_Word projection; live phase transport is checked separately",
        "complete_domain": True,
        "states": len(states),
        "moduli": moduli,
        "observation_classes": len({row.observation for row in observations}),
        "chart_visits": sum(row.chart_visits for row in observations),
        "max_chart_visits": max(row.chart_visits for row in observations),
        "candidates": [asdict(candidate) for candidate in candidates],
        "coordinate_refinement": refinement,
        "posthoc_moore_classes": None if moore is None else moore.classes,
        "posthoc_moore_refinement_rounds": None if moore is None else moore.rounds,
        "moore_scope": "after full chart construction; not an algebraic source classifier",
        "production_cutover": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--expanded-moore-baseline",
        action="store_true",
        help="explicitly rebuild the historical post-construction graph quotient",
    )
    args = parser.parse_args()
    print(
        json.dumps(
            audit_b1_quotient(expanded_moore_baseline=args.expanded_moore_baseline),
            indent=2,
        )
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
