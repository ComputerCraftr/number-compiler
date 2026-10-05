"""Opt-in differential and phase-transport audits for the B1 owner.

The executable owner is
``number_compiler.sequences.comma.semantic_continuation``.  This module is a
small adapter around that owner and the independent bounded chart observer;
it intentionally contains no second source-action compiler.  The optional
``--clock-quotient`` command constructs dense rows only for this bounded audit;
``--symbolic-clock-quotient`` measures the public symbolic builder and reports
actual admitted-shift work and any resource failure.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass

from devtools.verification.comma_b1_quotient import (
    B1Observation,
    B1State,
    observe_b1,
    offset_representatives,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    SemanticFunctionID,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD, BoundaryChart
from number_compiler.sequences.comma.domain import canonical_offset_orbit
from number_compiler.sequences.comma.semantic_continuation import (
    ContinuationID,
    SemanticContinuation,
    SemanticContinuationArena,
)
from number_compiler.sequences.comma.symbolic_return import (
    build_symbolic_returns,
    least_cyclic_rotation,
)

ActionLabel = tuple[str, int | None, int | None, int]


def canonical_roots() -> tuple[BoundaryChart, ...]:
    """Return the 46 canonical Entry roots used by the independent observer."""
    return tuple(
        BoundaryChart("entry", 1, 0, offset) for offset in offset_representatives()
    )


def production_semantic_owner(
    roots: tuple[BoundaryChart, ...] | None = None,
) -> SemanticContinuation:
    """Build the scoped production owner for caller-selected B1 roots."""
    selected = canonical_roots() if roots is None else roots
    arena = SemanticContinuationArena()
    arena.compile_many(selected)
    return arena.publish(selected)


@dataclass(frozen=True, slots=True)
class DifferentialResult:
    """Exact bounded comparison summary; mismatches retain their coordinates."""

    checked: int
    mismatches: tuple[tuple[int, int, B1Observation, str, int | None], ...]


@dataclass(frozen=True, slots=True)
class ClockShiftWitness:
    """One exact common clock translation between two return rows."""

    representative: int
    member: int
    shift: int


@dataclass(frozen=True, slots=True)
class CompleteReturnClockAudit:
    """Bounded complete-return partitions under one common phase translation.

    The dense return rows are constructed only inside the opt-in audit.  The
    result retains partitions and exact shift witnesses, never the rows.  A
    translation compares the same labeled output at every column after one
    cyclic phase shift; output labels are not renamed or permuted.
    """

    phase_count: int
    source_count: int
    exact_partitions: tuple[tuple[int, ...], ...]
    translated_partitions: tuple[tuple[int, ...], ...]
    shift_witnesses: tuple[ClockShiftWitness, ...]
    raw_exact_class_count: int
    raw_translated_class_count: int

    @property
    def exact_class_count(self) -> int:
        return len(self.exact_partitions)

    @property
    def translated_class_count(self) -> int:
        return len(self.translated_partitions)

    def as_json(self) -> dict[str, object]:
        return {
            "phase_count": self.phase_count,
            "source_count": self.source_count,
            "exact_return_classes": self.exact_class_count,
            "common_clock_translation_classes": self.translated_class_count,
            "exact_merges": self.source_count - self.exact_class_count,
            "translation_merges": self.exact_class_count - self.translated_class_count,
            "total_merges": self.source_count - self.translated_class_count,
            "canonical_live_fiber_projection": {
                "exact_classes": self.exact_class_count,
                "translated_classes": self.translated_class_count,
                "labels": "kind, canonical Live fiber, exact Stop J, exponent advance",
            },
            "raw_live_coordinate_exact_classes": self.raw_exact_class_count,
            "raw_live_coordinate_translation_classes": self.raw_translated_class_count,
            "raw_live_coordinate_output": {
                "exact_classes": self.raw_exact_class_count,
                "translated_classes": self.raw_translated_class_count,
                "labels": "kind, raw Live crossing coordinate, exact Stop J, exponent advance",
            },
            "exact_partitions": self.exact_partitions,
            "translated_partitions": self.translated_partitions,
            "shift_witnesses": tuple(
                {
                    "representative": witness.representative,
                    "member": witness.member,
                    "shift": witness.shift,
                }
                for witness in self.shift_witnesses
            ),
            "output_labels": "complete labeled terminal/live returns; no renaming",
            "production_cutover": False,
        }


@dataclass(frozen=True, slots=True)
class SymbolicClockQuotientAudit:
    """Resource and representative counts from the public symbolic builder.

    This opt-in developer audit canonicalizes each distinct owner-local return
    function over its admitted translation period.  It does not retain dense
    924-column rows and does not make the resulting local handles a production
    identity or an Isabelle refinement.
    """

    source_count: int
    action_id_count: int
    distinct_function_count: int
    canonical_function_count: int
    candidate_scans: int
    planned_candidate_scans: int
    max_candidate_scan: int
    phase_reads: int
    comparisons: int
    completed_function_count: int
    all_complete: bool
    error: str | None
    shift_cache_entries: int
    peak_shift_cache_entries: int
    clock_primitive_entries: int
    valid_mask_entries: int
    valid_mask_cache_hits: int
    valid_mask_cache_misses: int
    return_shift_cache_hits: int
    return_shift_cache_misses: int
    clock_shift_cache_hits: int
    clock_shift_cache_misses: int
    function_nodes: int

    def as_json(self) -> dict[str, object]:
        return {
            "source_count": self.source_count,
            "action_id_count": self.action_id_count,
            "distinct_function_count": self.distinct_function_count,
            "canonical_function_count": self.canonical_function_count,
            "candidate_scans": self.candidate_scans,
            "planned_candidate_scans": self.planned_candidate_scans,
            "max_candidate_scan": self.max_candidate_scan,
            "phase_reads": self.phase_reads,
            "comparisons": self.comparisons,
            "completed_function_count": self.completed_function_count,
            "all_candidates_complete": self.all_complete,
            "error": self.error,
            "shift_cache_entries": self.shift_cache_entries,
            "peak_shift_cache_entries": self.peak_shift_cache_entries,
            "clock_primitive_entries": self.clock_primitive_entries,
            "valid_mask_entries": self.valid_mask_entries,
            "valid_mask_cache_hits": self.valid_mask_cache_hits,
            "valid_mask_cache_misses": self.valid_mask_cache_misses,
            "return_shift_cache_hits": self.return_shift_cache_hits,
            "return_shift_cache_misses": self.return_shift_cache_misses,
            "clock_shift_cache_hits": self.clock_shift_cache_hits,
            "clock_shift_cache_misses": self.clock_shift_cache_misses,
            "function_nodes": self.function_nodes,
            "dense_phase_rows": False,
            "production_cutover": False,
        }


def differential_against_observe(
    view: SemanticContinuation | None = None,
    roots: tuple[BoundaryChart, ...] | None = None,
) -> DifferentialResult:
    """Compare every canonical B1 action with the independent chart observer."""
    selected = canonical_roots() if roots is None else roots
    compiled = production_semantic_owner(selected) if view is None else view
    mismatches: list[tuple[int, int, B1Observation, str, int | None]] = []
    checked = 0
    for source in selected:
        if (
            source.kind != "entry"
            or source.leading != 1
            or source.delta != 0
            or not 0 <= source.coordinate <= 90
        ):
            raise ValueError("differential roots must be canonical decade roots")
        canonical_fiber = canonical_offset_orbit(source.coordinate)
        for phase in range(PERIOD):
            checked += 1
            expected = observe_b1(B1State(canonical_fiber, phase)).observation
            actual = compiled.evaluate(source, phase).action
            observed_kind = "stop" if actual.kind == "stop" else actual.kind
            observed_value: int | None
            if actual.kind == "live" and actual.live_root is not None:
                observed_value = canonical_offset_orbit(actual.live_root)
            else:
                observed_value = actual.stop_j
            matches = (
                (
                    expected.kind == "live"
                    and actual.kind == "live"
                    and observed_value == expected.value
                )
                or (
                    expected.kind == "fork"
                    and actual.kind == "stop"
                    and observed_value == expected.value - 2
                )
                or (
                    expected.kind == "landmine"
                    and actual.kind == "stop"
                    and observed_value == 8
                )
            )
            if not matches:
                mismatches.append(
                    (canonical_fiber, phase, expected, observed_kind, observed_value)
                )
    return DifferentialResult(checked, tuple(mismatches))


def _complete_return_label(
    view: SemanticContinuation,
    identifier: ContinuationID,
    phase: int,
    *,
    canonical_live: bool,
) -> ActionLabel:
    """Read one terminal/live label with an explicit live-coordinate scope."""
    action = view.evaluate_id(identifier, phase)
    live_label = action.live_root
    if canonical_live and live_label is not None:
        live_label = canonical_offset_orbit(live_label)
    return action.kind, live_label, action.stop_j, action.exponent_advance


def _least_rotation(
    row: tuple[ActionLabel, ...],
) -> tuple[int, tuple[ActionLabel, ...]]:
    """Return the lexicographically least cyclic row and its start column."""
    size = len(row)
    if size == 0:
        raise ValueError("complete return rows cannot be empty")
    start = least_cyclic_rotation(
        size,
        row.__getitem__,
        compare=lambda left, right: (left > right) - (left < right),
    )
    return start, row[start:] + row[:start]


def _partition_rows(
    rows: dict[int, tuple[ActionLabel, ...]],
) -> tuple[
    tuple[tuple[int, ...], ...],
    tuple[tuple[int, ...], ...],
    tuple[ClockShiftWitness, ...],
]:
    exact_groups: dict[tuple[ActionLabel, ...], list[int]] = {}
    translated_groups: dict[tuple[ActionLabel, ...], list[int]] = {}
    rotations: dict[int, tuple[int, tuple[ActionLabel, ...]]] = {}
    for local_id, row in rows.items():
        exact_groups.setdefault(row, []).append(local_id)
        rotations[local_id] = _least_rotation(row)
        translated_groups.setdefault(rotations[local_id][1], []).append(local_id)
    exact_partitions = tuple(
        tuple(members)
        for members in sorted(exact_groups.values(), key=lambda group: group[0])
    )
    translated_partitions = tuple(
        tuple(members)
        for members in sorted(translated_groups.values(), key=lambda group: group[0])
    )
    witnesses: list[ClockShiftWitness] = []
    for members in translated_partitions:
        representative = members[0]
        representative_start = rotations[representative][0]
        for member in members[1:]:
            member_start = rotations[member][0]
            shift = (representative_start - member_start) % PERIOD
            if any(
                rows[member][phase] != rows[representative][(phase + shift) % PERIOD]
                for phase in range(PERIOD)
            ):
                raise AssertionError("clock translation witness failed exact labels")
            witnesses.append(ClockShiftWitness(representative, member, shift))
    return exact_partitions, translated_partitions, tuple(witnesses)


def audit_complete_return_clock_quotient(
    view: SemanticContinuation | None = None,
) -> CompleteReturnClockAudit:
    """Audit exact return rows and their common clock-translation quotient.

    This is an opt-in bounded experiment over the compiled source closure.  It
    does not add a production phase table: rows are equal only when every
    terminal/live label agrees after one common cyclic phase shift.
    """
    compiled = production_semantic_owner() if view is None else view
    identifiers = tuple(
        sorted(set(compiled.source_ids.values()), key=lambda item: item.local_id)
    )
    if not identifiers:
        raise ValueError("complete-return audit requires a nonempty source closure")
    canonical_rows = {
        identifier.local_id: tuple(
            _complete_return_label(compiled, identifier, phase, canonical_live=True)
            for phase in range(PERIOD)
        )
        for identifier in identifiers
    }
    raw_rows = {
        identifier.local_id: tuple(
            _complete_return_label(compiled, identifier, phase, canonical_live=False)
            for phase in range(PERIOD)
        )
        for identifier in identifiers
    }
    exact_partitions, translated_partitions, witnesses = _partition_rows(canonical_rows)
    raw_exact_partitions, raw_translated_partitions, _ = _partition_rows(raw_rows)
    return CompleteReturnClockAudit(
        PERIOD,
        len(identifiers),
        exact_partitions,
        translated_partitions,
        tuple(witnesses),
        len(raw_exact_partitions),
        len(raw_translated_partitions),
    )


def audit_symbolic_clock_quotient(
    view: SemanticContinuation | None = None,
) -> SymbolicClockQuotientAudit:
    """Measure symbolic return handles and admitted-period canonicalization.

    The public ``SemanticFunctionArena`` performs the only function
    construction.  We canonicalize one representative CID per distinct
    symbolic handle, so duplicate source bindings do not repeat the same
    orbit scan.  ``candidate_scans`` counts callbacks reached by the scan;
    ``planned_candidate_scans`` is the corresponding full support-period sum.
    If construction fails, the result reports the completed prefix and error.
    """
    compiled = production_semantic_owner() if view is None else view
    symbolic = build_symbolic_returns(compiled)
    representatives: dict[SemanticFunctionID, ContinuationID] = {}
    for identifier, function in symbolic.functions.items():
        representatives.setdefault(function, identifier)
    support_periods = tuple(
        symbolic.translation_period(function) for function in representatives
    )
    planned_scans = sum(support_periods)
    candidate_scans = 0
    phase_reads = 0
    comparisons = 0
    peak_shift_cache_entries = 0
    canonical_results = []

    def observe_candidate(_shift: int) -> None:
        nonlocal candidate_scans
        candidate_scans += 1

    error: str | None = None
    for identifier in representatives.values():
        try:
            result = symbolic.canonical_shift(
                identifier, candidate_observer=observe_candidate
            )
            canonical_results.append(result)
            phase_reads += result.phase_reads
            comparisons += result.comparisons
        except (MemoryError, RuntimeError, ValueError) as exc:
            error = f"{type(exc).__name__}: {exc}"
            break
        finally:
            peak_shift_cache_entries = max(
                peak_shift_cache_entries, len(symbolic.shift_cache)
            )
            # Candidate handles remain valid in the arena node store; the
            # memo only owns temporary lookup references for this orbit.
            symbolic.shift_cache.clear()
    canonical = tuple(canonical_results)
    cache_counters = symbolic.arena.ledger.counters
    return SymbolicClockQuotientAudit(
        source_count=len(compiled.source_ids),
        action_id_count=len(symbolic.functions),
        distinct_function_count=len(representatives),
        canonical_function_count=len({result.function for result in canonical}),
        candidate_scans=candidate_scans,
        planned_candidate_scans=planned_scans,
        max_candidate_scan=max(support_periods, default=0),
        phase_reads=phase_reads,
        comparisons=comparisons,
        completed_function_count=len(canonical),
        all_complete=error is None
        and len(canonical) == len(representatives)
        and all(result.complete for result in canonical),
        error=error,
        shift_cache_entries=len(symbolic.shift_cache),
        peak_shift_cache_entries=peak_shift_cache_entries,
        clock_primitive_entries=len(symbolic.clock_shift_cache),
        valid_mask_entries=len(symbolic.valid_mask_cache),
        valid_mask_cache_hits=cache_counters.get(
            "comma_symbolic_valid_mask_cache_hits", 0
        ),
        valid_mask_cache_misses=cache_counters.get(
            "comma_symbolic_valid_mask_cache_misses", 0
        ),
        return_shift_cache_hits=cache_counters.get(
            "comma_symbolic_return_shift_cache_hits", 0
        ),
        return_shift_cache_misses=cache_counters.get(
            "comma_symbolic_return_shift_cache_misses", 0
        ),
        clock_shift_cache_hits=cache_counters.get(
            "comma_symbolic_clock_shift_cache_hits", 0
        ),
        clock_shift_cache_misses=cache_counters.get(
            "comma_symbolic_clock_shift_cache_misses", 0
        ),
        function_nodes=len(symbolic.arena.nodes),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--differential",
        action="store_true",
        help="run the full 46*924 production-vs-chart audit",
    )
    parser.add_argument(
        "--clock-quotient",
        action="store_true",
        help="audit complete labels and common phase-translation witnesses",
    )
    parser.add_argument(
        "--symbolic-clock-quotient",
        action="store_true",
        help="measure public symbolic return handles and admitted shift scans",
    )
    args = parser.parse_args()
    view = production_semantic_owner()
    if args.symbolic_clock_quotient:
        symbolic_result = audit_symbolic_clock_quotient(view)
        print(json.dumps(symbolic_result.as_json(), indent=2))
        if not symbolic_result.all_complete:
            raise SystemExit(1)
        return
    if args.clock_quotient:
        print(
            json.dumps(audit_complete_return_clock_quotient(view).as_json(), indent=2)
        )
        return
    payload: dict[str, object] = {
        "sources": len(view.transitions),
        "continuation_ids": len(view.actions_by_id),
    }
    if args.differential:
        differential_result = differential_against_observe(view)
        payload.update(
            {
                "checked": differential_result.checked,
                "mismatches": differential_result.mismatches,
            }
        )
    print(json.dumps(payload, default=str, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
