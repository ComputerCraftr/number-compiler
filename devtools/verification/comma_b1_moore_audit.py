"""Bounded B1 source-action separation audit.

This is a differential audit of the source-selected endpoint constructor.  It
evaluates the 46 canonical sector-1 representatives at phases 0 and 1 and
records an exact separating phase for every unordered pair.  A report is a
finite witness for the declared terminal B1 action only; it is not a proof of
the 36-word/19-state language claims and it does not define a production
source controller.

The full-domain commands are deliberately opt-in rather than run by default.
Their 46*924 cells are useful experiments, but a finite run does not establish
online source selection or quotient minimality.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from dataclasses import asdict, dataclass
from itertools import combinations

from number_compiler.arithmetic.functions.finite_observer import (
    class_members,
    minimize_finite_observer,
)
from number_compiler.sequences.comma.arithmetic import (
    cycle_residue_period,
    cycle_transfer,
)
from number_compiler.sequences.comma.boundary_chart import (
    BoundaryChart,
    chart_step,
)
from number_compiler.sequences.comma.cyclotomic_clock import CyclotomicClock
from number_compiler.sequences.comma.decisive_endpoint import (
    EndpointRun,
    evaluate_b1_source,
)

from .comma_b1_quotient import chart_measure, offset_orbit, offset_representatives

AUDIT_PHASES: tuple[int, int] = (0, 1)
FULL_AUDIT_COUNT = 46 * 924
STRUCTURAL_ALPHABET: tuple[int, ...] = (1, 2, 3, 6, 22, 28)
MAX_STRUCTURAL_STEPS = 64


@dataclass(frozen=True, slots=True)
class B1Action:
    """The terminal action exposed by the projected B1 orbit word.

    The live coordinate is projected through ``offset_orbit``. Raw crossing
    coordinates and strict sector counts are occurrence/construction data and
    are intentionally absent from this Moore observation.
    """

    kind: str
    live_fiber: int | None
    fork_a: int | None
    exponent_advance: int

    @classmethod
    def from_run(cls, run: EndpointRun) -> B1Action:
        outcome = run.outcome
        live_fiber = (
            offset_orbit(outcome.entry_coordinate)
            if outcome.kind == "live" and outcome.entry_coordinate is not None
            else None
        )
        return cls(
            outcome.kind,
            live_fiber,
            outcome.fork_a,
            outcome.exponent_advance,
        )


@dataclass(frozen=True, slots=True)
class B1PhaseObservation:
    """One representative's exact action at one declared phase."""

    fiber: int
    offset: int
    phase: int
    action: B1Action


@dataclass(frozen=True, slots=True)
class B1PairWitness:
    """A phase that separates two source representatives."""

    left: B1PhaseObservation
    right: B1PhaseObservation


@dataclass(frozen=True, slots=True)
class B1PairCollision:
    """Two representatives equal at every audited phase."""

    left: B1PhaseObservation
    right: B1PhaseObservation


@dataclass(frozen=True, slots=True)
class B1MooreAudit:
    """Complete pairwise result for the two-phase terminal-action audit."""

    phases: tuple[int, ...]
    representatives: tuple[int, ...]
    observations: tuple[B1PhaseObservation, ...]
    witnesses: tuple[B1PairWitness, ...]
    collisions: tuple[B1PairCollision, ...]
    full_audit_count: int

    @property
    def pair_count(self) -> int:
        return len(self.witnesses) + len(self.collisions)

    @property
    def unique_action_counts(self) -> dict[int, int]:
        return {
            phase: len(
                {
                    observation.action
                    for observation in self.observations
                    if observation.phase == phase
                }
            )
            for phase in self.phases
        }


@dataclass(frozen=True, slots=True)
class StructuralEntry:
    """Entry context recorded before its shared arithmetic step."""

    phase: int
    leading: int
    coordinate: int
    period: int


@dataclass(frozen=True, slots=True)
class StructuralTrace:
    """One test-only period word and its exact projected terminal action."""

    word: tuple[int, ...]
    entries: tuple[StructuralEntry, ...]
    action: B1Action


@dataclass(frozen=True, slots=True)
class StructuralSuffixWitness:
    """A suffix over period symbols separating two trie states."""

    left_state: int
    right_state: int
    left_class: int
    right_class: int
    suffix: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class StructuralWordAudit:
    """Posthoc structural-word language audit, never a source controller."""

    source_cells: int
    structural_words: int
    trie_states: int
    minimized_suffix_states: int
    alphabet: tuple[int, ...]
    word_action_conflicts: tuple[dict[str, object], ...]
    suffix_witnesses: tuple[StructuralSuffixWitness, ...]
    suffix_witnesses_truncated: bool
    source_dispatch_guard: tuple[str, ...]
    language_only: bool
    production_cutover: bool


def _observe(offset: int, fiber: int, phase: int) -> B1PhaseObservation:
    if type(offset) is not int or type(fiber) is not int:
        raise ValueError("B1 audit coordinates must be exact integers")
    if type(phase) is not int or phase < 0:
        raise ValueError("B1 audit phase must be a nonnegative integer")
    run = evaluate_b1_source(CyclotomicClock.from_phase(phase), offset)
    return B1PhaseObservation(fiber, offset, phase, B1Action.from_run(run))


def audit_b1_phase_pairs(
    phases: tuple[int, ...] = AUDIT_PHASES,
) -> B1MooreAudit:
    """Evaluate representatives and emit exact witnesses or collisions.

    The evaluator is called once per representative and phase.  Pair search
    is only 1,035 comparisons; it never builds a transition graph or stores a
    source-word history.
    """

    if not phases or any(type(phase) is not int or phase < 0 for phase in phases):
        raise ValueError("B1 audit requires nonnegative integer phases")
    if len(set(phases)) != len(phases):
        raise ValueError("B1 audit phases must be distinct")
    representatives = offset_representatives()
    observations = tuple(
        _observe(offset, fiber, phase)
        for fiber, offset in enumerate(representatives)
        for phase in phases
    )
    by_key = {
        (observation.fiber, observation.phase): observation
        for observation in observations
    }
    witnesses: list[B1PairWitness] = []
    collisions: list[B1PairCollision] = []
    for left_fiber, right_fiber in combinations(range(len(representatives)), 2):
        left_by_phase = [by_key[left_fiber, phase] for phase in phases]
        right_by_phase = [by_key[right_fiber, phase] for phase in phases]
        witness = next(
            (
                B1PairWitness(left, right)
                for left, right in zip(left_by_phase, right_by_phase, strict=True)
                if left.action != right.action
            ),
            None,
        )
        if witness is None:
            collisions.append(B1PairCollision(left_by_phase[0], right_by_phase[0]))
        else:
            witnesses.append(witness)
    return B1MooreAudit(
        phases,
        representatives,
        observations,
        tuple(witnesses),
        tuple(collisions),
        FULL_AUDIT_COUNT,
    )


def full_audit_command() -> str:
    """Return the intentionally-unrun 46*924 experiment command."""

    return (
        "PYTHONPATH=src python3 -m devtools.verification.comma_b1_moore_audit "
        "--full-source-grid"
    )


def structural_audit_command() -> str:
    """Return the intentionally-unrun structural-word experiment command."""

    return (
        "PYTHONPATH=src python3 -m devtools.verification.comma_b1_moore_audit "
        "--structural-moore"
    )


def audit_full_source_grid() -> dict[str, object]:
    """Run the explicit 46*924 source grid when a coordinator requests it.

    This is an on-demand arithmetic experiment, not a cached constructor.  It
    retains only exact terminal actions while counting them; no structural
    word, transition table, or minimized graph is produced.
    """

    representatives = offset_representatives()
    action_counts: dict[B1Action, int] = {}
    for offset in representatives:
        for phase in range(924):
            action = B1Action.from_run(
                evaluate_b1_source(CyclotomicClock.from_phase(phase), offset)
            )
            action_counts[action] = action_counts.get(action, 0) + 1
    return {
        "scope": "explicit 46*924 source grid; terminal actions only",
        "cells": FULL_AUDIT_COUNT,
        "representatives": representatives,
        "phases": 924,
        "unique_terminal_actions": len(action_counts),
        "action_counts": {
            repr(action): count for action, count in action_counts.items()
        },
        "production_cutover": False,
    }


def structural_trace(offset: int, phase: int) -> StructuralTrace:
    """Record Entry period symbols by walking the shared chart arithmetic.

    The period word is intentionally only a language observation.  Entry
    coordinates, source phase, and the projected terminal action are retained
    in the test trace so a report can expose why that word is insufficient for
    guarded continuation.
    """

    if type(offset) is not int or not 0 <= offset <= 90:
        raise ValueError("structural B1 trace requires an admitted source offset")
    if type(phase) is not int or not 0 <= phase < 924:
        raise ValueError("structural B1 trace requires phase in 0..923")
    chart = BoundaryChart("entry", 1, 0, offset)
    entries: list[StructuralEntry] = []
    symbols: list[int] = []
    for _ in range(MAX_STRUCTURAL_STEPS):
        if chart.kind == "entry":
            transfer = cycle_transfer(chart.leading, chart.coordinate % 10)
            period = cycle_residue_period(transfer.displacement)
            if period not in STRUCTURAL_ALPHABET:
                raise AssertionError("Entry period left the admitted alphabet")
            entries.append(
                StructuralEntry(
                    phase,
                    chart.leading,
                    chart.coordinate,
                    period,
                )
            )
            symbols.append(period)
        move = chart_step(phase, chart)
        target = move.next_chart
        if target is None:
            action = (
                B1Action("fork", None, move.fork_a, 0)
                if move.fork_a is not None
                else B1Action("landmine", None, None, 0)
            )
            return StructuralTrace(tuple(symbols), tuple(entries), action)
        if target.delta != 0:
            if (target.kind, target.leading, target.delta) != ("entry", 1, 1):
                raise AssertionError("structural B1 crossing changed its seam")
            return StructuralTrace(
                tuple(symbols),
                tuple(entries),
                B1Action("live", offset_orbit(target.coordinate), None, 1),
            )
        if not chart_measure(target) < chart_measure(chart):
            raise AssertionError("structural chart walk failed to decrease")
        chart = target
    raise AssertionError("structural B1 chart walk exceeded its finite bound")


def _structural_trie(
    word_actions: dict[tuple[int, ...], set[B1Action]],
) -> tuple[
    tuple[tuple[int | None, ...], ...],
    tuple[object, ...],
    tuple[int, ...],
    dict[tuple[int, ...], int],
]:
    """Build the finite trie consumed by the shared suffix minimizer."""

    prefixes: set[tuple[int, ...]] = {()}
    for word in word_actions:
        prefixes.update(word[:index] for index in range(1, len(word) + 1))
    ordered = sorted(prefixes, key=lambda value: (len(value), value))
    state_ids = {prefix: index for index, prefix in enumerate(ordered)}
    alphabet = tuple(sorted({symbol for word in word_actions for symbol in word}))
    rows: list[tuple[int | None, ...]] = []
    outputs: list[object] = []
    for prefix in ordered:
        rows.append(tuple(state_ids.get(prefix + (symbol,)) for symbol in alphabet))
        actions = word_actions.get(prefix)
        # The 19-state claim concerns the accepting language of period words.
        # Terminal payload sets are retained separately in ``word_actions``
        # and reported as conflicts; they must not inflate language states.
        outputs.append(actions is not None)
    return tuple(rows), tuple(outputs), alphabet, state_ids


def _suffix_witness(
    left: int,
    right: int,
    class_ids: tuple[int, ...],
    rows: tuple[tuple[int | None, ...], ...],
    outputs: tuple[object, ...],
    alphabet: tuple[int, ...],
) -> tuple[int, ...] | None:
    """Find one exact distinguishing suffix by a bounded product walk."""

    if outputs[left] != outputs[right]:
        return ()
    pending: deque[tuple[int, int, tuple[int, ...]]] = deque([(left, right, ())])
    seen = {(left, right)}
    while pending:
        current_left, current_right, suffix = pending.popleft()
        for index, symbol in enumerate(alphabet):
            target_left = rows[current_left][index]
            target_right = rows[current_right][index]
            candidate = suffix + (symbol,)
            if (target_left is None) != (target_right is None):
                return candidate
            if target_left is None or target_right is None:
                continue
            pair = (target_left, target_right)
            if outputs[target_left] != outputs[target_right]:
                return candidate
            if pair not in seen:
                seen.add(pair)
                pending.append((target_left, target_right, candidate))
    if class_ids[left] != class_ids[right]:
        raise AssertionError("unstable suffix partition lost a witness")
    return None


def audit_structural_words() -> StructuralWordAudit:
    """Run the opt-in 46*924 period-word and suffix-state experiment."""

    representatives = offset_representatives()
    word_actions: dict[tuple[int, ...], set[B1Action]] = {}
    word_samples: dict[
        tuple[int, ...], dict[B1Action, tuple[int, int, StructuralTrace]]
    ] = {}
    for offset in representatives:
        for phase in range(924):
            trace = structural_trace(offset, phase)
            word_actions.setdefault(trace.word, set()).add(trace.action)
            word_samples.setdefault(trace.word, {}).setdefault(
                trace.action, (offset, phase, trace)
            )

    rows, outputs, alphabet, _state_ids = _structural_trie(word_actions)
    minimized = minimize_finite_observer(rows, outputs)
    members = class_members(minimized.class_ids, minimized.classes)
    suffix_witnesses: list[StructuralSuffixWitness] = []
    class_pairs = (
        (left, right) for left, right in combinations(range(minimized.classes), 2)
    )
    for left_class, right_class in class_pairs:
        left_state = members[left_class][0]
        right_state = members[right_class][0]
        suffix = _suffix_witness(
            left_state,
            right_state,
            minimized.class_ids,
            rows,
            outputs,
            alphabet,
        )
        if suffix is None:
            raise AssertionError("distinct suffix classes lack a witness")
        suffix_witnesses.append(
            StructuralSuffixWitness(
                left_state,
                right_state,
                left_class,
                right_class,
                suffix,
            )
        )

    conflicts: list[dict[str, object]] = []
    for word, actions in sorted(word_actions.items()):
        if len(actions) <= 1:
            continue
        samples = word_samples[word]
        conflicts.append(
            {
                "word": word,
                "actions": tuple(sorted(actions, key=repr)),
                "samples": tuple(
                    {
                        "offset": offset,
                        "phase": phase,
                        "entries": trace.entries,
                    }
                    for offset, phase, trace in samples.values()
                ),
            }
        )
    guard = (
        "dispatch input must retain source phase r mod 924 for core-period projection",
        "dispatch input must retain each current Entry (leading, coordinate, delta) before its step",
        "dispatch output must include projected live fiber or fork_a/landmine and exponent advance",
        "period word recognition alone supplies no guarded source continuation or occurrence transport",
    )
    return StructuralWordAudit(
        FULL_AUDIT_COUNT,
        len(word_actions),
        len(rows),
        minimized.classes,
        alphabet,
        tuple(conflicts),
        tuple(suffix_witnesses),
        False,
        guard,
        True,
        False,
    )


def _json_report(audit: B1MooreAudit) -> dict[str, object]:
    return {
        "scope": "terminal B1 action separation only; no language quotient or production cutover",
        "phases": audit.phases,
        "representatives": audit.representatives,
        "representative_fibers": tuple(
            offset_orbit(offset) for offset in audit.representatives
        ),
        "observations": [asdict(item) for item in audit.observations],
        "pair_count": audit.pair_count,
        "witness_count": len(audit.witnesses),
        "collision_count": len(audit.collisions),
        "witnesses": [asdict(item) for item in audit.witnesses],
        "collisions": [asdict(item) for item in audit.collisions],
        "unique_action_counts": audit.unique_action_counts,
        "full_audit_count": audit.full_audit_count,
        "full_audit_command": full_audit_command(),
        "full_source_grid_executed": False,
    }


def _json_structural_report(audit: StructuralWordAudit) -> dict[str, object]:
    return {
        "scope": "period-word recognition audit only; no guarded source controller",
        **asdict(audit),
        "structural_audit_command": structural_audit_command(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--full-source-grid",
        action="store_true",
        help="evaluate all 46*924 source/fiber cells instead of the pair audit",
    )
    parser.add_argument(
        "--structural-moore",
        action="store_true",
        help="opt in to the 46*924 Entry-period trie and suffix audit",
    )
    args = parser.parse_args()
    if args.full_source_grid and args.structural_moore:
        parser.error("choose one optional full audit")
    if args.structural_moore:
        print(json.dumps(_json_structural_report(audit_structural_words()), indent=2))
        return
    if args.full_source_grid:
        print(json.dumps(audit_full_source_grid(), indent=2))
        return
    print(json.dumps(_json_report(audit_b1_phase_pairs()), indent=2))


__all__ = [
    "AUDIT_PHASES",
    "FULL_AUDIT_COUNT",
    "B1Action",
    "B1MooreAudit",
    "B1PairCollision",
    "B1PairWitness",
    "B1PhaseObservation",
    "StructuralEntry",
    "StructuralSuffixWitness",
    "StructuralTrace",
    "StructuralWordAudit",
    "audit_b1_phase_pairs",
    "audit_full_source_grid",
    "audit_structural_words",
    "full_audit_command",
    "structural_audit_command",
    "structural_trace",
]


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
