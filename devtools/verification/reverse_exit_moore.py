"""Finite D5 return refinement with explicit, uninterpreted EXIT continuations.

This oracle does not construct the recursive publisher. An exit variable names
an exact returned pair field, held separately from the finite port observation.
There is no source authority, chart or complete output morphism in this oracle.
The open partition is valid for arbitrary independent interpretations of those
variables; it is NOT an all-width temporal quotient or a production ActionID.
"""

from __future__ import annotations

import json
from collections.abc import Hashable, Sequence
from dataclasses import asdict, dataclass, replace
from itertools import product

from devtools.verification import exact_oracle, require_exact_oracle
from devtools.verification.carry_harmonic_ports import CarryHarmonicPortAction
from devtools.verification.oracles.sequence_arithmetic import reference_successor
from number_compiler.arithmetic.carry.carry_monoid import value_carry_fn
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseWidthPhase,
    ReverseWidthPhaseAction,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.functions.finite_observer import (
    FiniteObserverMinimization,
    minimize_finite_observer,
)


@dataclass(frozen=True, slots=True)
class ChamberReturnGraph:
    """Finite observations and internal edges; exact exit payloads are separate."""

    sources: tuple[tuple[int, ...], ...]
    observations: tuple[Hashable, ...]
    successors: tuple[int, ...]
    exit_payloads: tuple[tuple[int, ...], ...]

    def refine(self, exit_labels: Sequence[Hashable]) -> FiniteObserverMinimization:
        """Substitute a declared interpretation of EVERY external continuation.

        Boundary self-edges below encode free variables for finite refinement,
        not arithmetic self-loops. The two sorts cannot merge. Equal supplied
        labels assert continuation equality; this routine cannot prove it.
        """
        require_exact_oracle()
        if len(exit_labels) != len(self.exit_payloads):
            raise ValueError("every EXIT requires an explicit continuation label")
        size = len(self.sources)
        rows = tuple((target,) for target in self.successors) + tuple(
            (size + index,) for index in range(len(exit_labels))
        )
        labels = tuple(("active", value) for value in self.observations) + tuple(
            ("continuation-variable", label) for label in exit_labels
        )
        return minimize_finite_observer(rows, labels)


def carry_observation(field: tuple[int, ...]) -> Hashable:
    """The archive's Q11/border observation, including neutral target fields."""
    require_exact_oracle()
    ports = CarryHarmonicPortAction.from_domains(
        value_carry_fn(symbol, 10) for symbol in field
    )
    # Two outgoing values represent the complete three-element carry function.
    # The border keeps correlated F5 channels, including the neutral puncture.
    return (
        (ports.rows[0][0], ports.rows[1][0], sum(field) % 5),
        ports.border_rows(),
    )


def build_d5_return_graph() -> ChamberReturnGraph:
    """Bounded literal oracle: never imported or called by production."""
    require_exact_oracle()
    sources = tuple(
        (left, near, center, near, left)
        for left, near, center in product(range(19), range(19), range(0, 19, 2))
    )
    indices: dict[tuple[int, ...], int] = {
        field: index for index, field in enumerate(sources)
    }
    exits: dict[tuple[int, ...], int] = {}
    successors: list[int] = []
    for field in sources:
        target = reference_successor(field)
        index = indices.get(target)
        if index is None:
            index = len(sources) + exits.setdefault(target, len(exits))
        successors.append(index)
    return ChamberReturnGraph(
        sources,
        tuple(carry_observation(field) for field in sources),
        tuple(successors),
        tuple(exits),
    )


@dataclass(frozen=True, slots=True)
class ExitRefinementReport:
    sources: int
    exit_occurrences: int
    absorbing_exit_classes: int
    returned_ports_classes: int
    independent_continuation_classes: int
    open_refinement_rounds: int
    merged_exit_conflicts: int
    first_conflict: tuple[tuple[int, ...], tuple[int, ...]] | None
    no_growth_rows: int
    growth_rows: int
    no_growth_classes: int
    growth_classes: int
    width_refined_classes: int
    production_admission: bool = False


def audit_exit_refinement() -> ExitRefinementReport:
    """Compare the old lost EXIT with actual returned ports and open variables."""
    require_exact_oracle()
    graph = build_d5_return_graph()
    size = len(graph.sources)
    collapsed = graph.refine(("EXIT",) * len(graph.exit_payloads))
    port_labels = tuple(carry_observation(field) for field in graph.exit_payloads)
    projected = graph.refine(port_labels)
    opened = graph.refine(tuple(range(len(graph.exit_payloads))))
    first: tuple[tuple[int, ...], tuple[int, ...]] | None = None
    conflicts = 0
    representatives: dict[int, tuple[int, Hashable]] = {}
    for index, target in enumerate(graph.successors):
        if target < size:
            continue
        label = port_labels[target - size]
        old_index, old_label = representatives.setdefault(
            collapsed.class_ids[index], (index, label)
        )
        if old_label != label:
            conflicts += 1
            if first is None:
                first = graph.sources[old_index], graph.sources[index]
    growths = tuple(int(target >= size) for target in graph.successors)
    by_class: dict[int, set[int]] = {}
    for class_id, growth in zip(collapsed.class_ids[:size], growths, strict=True):
        by_class.setdefault(class_id, set()).add(growth)
    if any(len(values) != 1 for values in by_class.values()):
        raise AssertionError("the D5 quotient mixes growth and no-growth")
    width_graph = replace(
        graph,
        observations=tuple(
            (label, ReverseWidthPhaseAction.from_growth_count(growth))
            for label, growth in zip(graph.observations, growths, strict=True)
        ),
    )
    width_refined = width_graph.refine(
        tuple(
            (port, ReverseWidthPhase.from_extent(len(field)))
            for port, field in zip(port_labels, graph.exit_payloads, strict=True)
        )
    )
    return ExitRefinementReport(
        size,
        len(graph.exit_payloads),
        len(set(collapsed.class_ids[:size])),
        len(set(projected.class_ids[:size])),
        len(set(opened.class_ids[:size])),
        opened.rounds,
        conflicts,
        first,
        growths.count(0),
        growths.count(1),
        sum(values == {0} for values in by_class.values()),
        sum(values == {1} for values in by_class.values()),
        len(set(width_refined.class_ids[:size])),
    )


@dataclass(frozen=True, slots=True)
class WidthPhaseAudit:
    seed: int
    widths: tuple[tuple[int, int], ...]
    phases: tuple[int, ...]
    growth_count: int


def audit_width_phases(seed: int, *, steps: int = 256) -> WidthPhaseAudit:
    """Literal pair recurrence to reproduce a bounded width-phase claim."""
    require_exact_oracle()
    if type(seed) is not int or not 0 <= seed < 10**12:
        raise ValueError("width audit requires a bounded nonnegative seed")
    if type(steps) is not int or not 0 <= steps <= 1024:
        raise ValueError("width audit supports at most 1024 literal transitions")
    digits = digits_lsd(seed, 10)
    pair = tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))
    initial_width = len(pair)
    phase = ReverseWidthPhase.from_extent(initial_width)
    reached = {phase.phase}
    total_growth = 0
    widths = [(0, initial_width)]
    for step in range(1, steps + 1):
        target = reference_successor(pair)
        growth = len(target) - len(pair)
        if growth not in (0, 1):
            raise AssertionError("literal primitive growth is not a bit")
        total_growth += growth
        phase = phase.apply(ReverseWidthPhaseAction.from_growth_count(growth))
        if phase != ReverseWidthPhase.from_extent(len(target)):
            raise AssertionError("width phase disagrees with literal target")
        pair = target
        reached.add(phase.phase)
        if step in (8, 16, 32, 64, 128, 256) or step == steps:
            widths.append((step, len(pair)))
    if initial_width + total_growth != len(pair):
        raise AssertionError("accumulated growth disagrees with exact extent")
    return WidthPhaseAudit(seed, tuple(widths), tuple(sorted(reached)), total_growth)


def _command() -> None:
    with exact_oracle():
        print(json.dumps(asdict(audit_exit_refinement()), indent=2))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(_command))
