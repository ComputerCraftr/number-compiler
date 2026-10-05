"""Bounded reproduction of the Compact B1 root scope graph.

This is an audit teacher, not a production constructor.  It follows the
source-selected endpoint law using the shared ``entry_headroom`` and
``classify_near_port`` arithmetic, then applies one shared ``chart_step``.
The external clock is represented by an integer residue in ``0..923`` and is
partitioned by the short core period at each Entry.  No response rows, rank
tables, or 924-bit masks are consulted.

The default command reproduces the root-0 graph statistics from the compact
recurrence.  ``--all-roots`` is opt-in because it repeats the bounded graph
walk for all 46 canonical decade representatives.

``terminal_leaves`` counts terminal action packets.  ``terminal_phase_count``
counts the phases carried by those packets; the latter must be 924 for every
root, while the former is 495 for root 0.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from typing import Literal

from devtools.verification.comma_b1_quotient import (
    chart_measure,
    offset_orbit,
    offset_representatives,
)
from number_compiler.sequences.comma.arithmetic import (
    classify_near_port,
    cycle_residue_period,
    cycle_transfer,
    entry_headroom,
)
from number_compiler.sequences.comma.boundary_chart import (
    PERIOD,
    BoundaryChart,
    chart_step,
)
from number_compiler.sequences.comma.domain import decade_root_coordinate

Scope = tuple[int, ...]
TerminalLabel = tuple[Literal["fork", "landmine", "live"], int | None]


@dataclass(frozen=True, slots=True)
class RootScopeAudit:
    """Counts and bounded diagnostics for one source root."""

    root_index: int
    offset: int
    recursive_calls: int
    unique_source_states: int
    terminal_leaves: int
    output_labels: int
    distinct_scopes: int
    singleton_scopes: int
    max_source_occurrences: int
    repeated_source_visits: int
    unique_source_scope_pairs: int
    reused_source_scope_visits: int
    outcome_counts: tuple[tuple[str, int], ...]
    terminal_phase_count: int

    def as_json(self) -> dict[str, object]:
        return {
            "root_index": self.root_index,
            "offset": self.offset,
            "recursive_calls": self.recursive_calls,
            "unique_source_states": self.unique_source_states,
            "terminal_leaves": self.terminal_leaves,
            "output_labels": self.output_labels,
            "distinct_scopes": self.distinct_scopes,
            "singleton_scopes": self.singleton_scopes,
            "max_source_occurrences": self.max_source_occurrences,
            "repeated_source_visits": self.repeated_source_visits,
            "unique_source_scope_pairs": self.unique_source_scope_pairs,
            "reused_source_scope_visits": self.reused_source_scope_visits,
            "outcome_coverage": dict(self.outcome_counts),
            "terminal_phase_count": self.terminal_phase_count,
            "scope_representation": "concrete phase tuples for audit only",
        }


def _source_selected_target(source: BoundaryChart, phase: int) -> BoundaryChart:
    """Construct the exact decisive Near target for one source occurrence.

    Entry headroom includes the source's decade delta.  Near sources are
    closed by the same terminal-germ selector used by the endpoint producer.
    The returned chart is then consumed by ``chart_step``; this avoids the
    generic Entry chart teacher's extra intermediate state.
    """
    if source.kind == "entry":
        _, headroom = entry_headroom(
            source.leading,
            source.coordinate,
            phase,
            exponent_delta=source.delta,
        )
    else:
        headroom = source.coordinate
    terminal_headroom = classify_near_port(source.leading, headroom).terminal_headroom
    return BoundaryChart("near", source.leading, source.delta, terminal_headroom)


def _source_period(source: BoundaryChart) -> int:
    if source.kind == "near":
        return 1
    transfer = cycle_transfer(source.leading, source.coordinate % 10)
    return cycle_residue_period(transfer.displacement)


def _terminal_label(
    move_next: BoundaryChart | None,
    fork_a: int | None,
) -> TerminalLabel | None:
    if move_next is None:
        return ("fork", fork_a) if fork_a is not None else ("landmine", None)
    if move_next.kind == "entry" and move_next.delta == 1:
        if not decade_root_coordinate(move_next.leading, move_next.coordinate):
            raise AssertionError("live crossing left the canonical root domain")
        return ("live", offset_orbit(move_next.coordinate))
    return None


def _walk_root(
    root_index: int, offset: int
) -> tuple[
    RootScopeAudit,
    set[BoundaryChart],
    set[tuple[BoundaryChart, Scope]],
]:
    """Walk one root and return statistics plus exact keys from that walk."""
    if type(root_index) is not int or not 0 <= root_index < 46:
        raise ValueError("root index must be in 0..45")
    if type(offset) is not int or offset != offset_representatives()[root_index]:
        if type(offset) is not int:
            raise TypeError("root offset must be an integer")
        raise ValueError("root offset is not the canonical representative")

    root = BoundaryChart("entry", 1, 0, offset)
    pending: list[tuple[BoundaryChart, Scope]] = [(root, tuple(range(PERIOD)))]
    source_occurrences: dict[BoundaryChart, int] = {}
    source_scope_keys: set[tuple[BoundaryChart, Scope]] = set()
    scopes: set[Scope] = set()
    labels: set[TerminalLabel] = set()
    outcome_counts: dict[str, int] = {}
    reused_source_scope_visits = 0
    terminal_leaves = 0
    terminal_phase_count = 0

    while pending:
        source, scope = pending.pop()
        if not scope:
            raise AssertionError("empty scope entered the recurrence")
        source_scope_key = (source, scope)
        if source_scope_key in source_scope_keys:
            reused_source_scope_visits += 1
        else:
            source_scope_keys.add(source_scope_key)
        source_occurrences[source] = source_occurrences.get(source, 0) + 1
        scopes.add(scope)
        period = _source_period(source)
        packets: dict[int, list[int]] = {residue: [] for residue in range(period)}
        for phase in scope:
            packets[phase % period].append(phase)
        for residue, packet in packets.items():
            if not packet:
                continue
            target = _source_selected_target(source, residue)
            move = chart_step(residue, target)
            label = _terminal_label(move.next_chart, move.fork_a)
            if label is not None:
                terminal_leaves += 1
                terminal_phase_count += len(packet)
                labels.add(label)
                outcome_counts[label[0]] = outcome_counts.get(label[0], 0) + 1
                continue
            next_chart = move.next_chart
            if next_chart is None:
                raise AssertionError("nonterminal move lost its next chart")
            if not (
                next_chart.kind == "near"
                or (next_chart.kind == "entry" and next_chart.delta == 0)
            ):
                raise AssertionError("unexpected nonterminal decade transition")
            if not chart_measure(next_chart) < chart_measure(target):
                raise AssertionError("B1 chart measure did not decrease")
            pending.append((next_chart, tuple(packet)))

    unique_source_states = len(source_occurrences)
    recursive_calls = sum(source_occurrences.values())
    if terminal_phase_count != PERIOD:
        raise AssertionError("terminal packets do not cover all 924 phases")
    source_scope_sources = {source for source, _ in source_scope_keys}
    return (
        RootScopeAudit(
            root_index=root_index,
            offset=offset,
            recursive_calls=recursive_calls,
            unique_source_states=unique_source_states,
            terminal_leaves=terminal_leaves,
            output_labels=len(labels),
            distinct_scopes=len(scopes),
            singleton_scopes=sum(len(scope) == 1 for scope in scopes),
            max_source_occurrences=max(source_occurrences.values()),
            repeated_source_visits=recursive_calls - unique_source_states,
            unique_source_scope_pairs=len(source_scope_keys),
            reused_source_scope_visits=reused_source_scope_visits,
            outcome_counts=tuple(sorted(outcome_counts.items())),
            terminal_phase_count=terminal_phase_count,
        ),
        source_scope_sources,
        source_scope_keys,
    )


def audit_root(root_index: int, offset: int) -> RootScopeAudit:
    """Walk one Compact B1 root without Python recursion or phase masks."""
    result, _, _ = _walk_root(root_index, offset)
    return result


def audit_scope_graph(
    *, root_index: int = 0, all_roots: bool = False
) -> dict[str, object]:
    """Return root-0 statistics, or an explicit all-root duplication audit."""
    representatives = offset_representatives()
    if all_roots:
        walks = tuple(
            _walk_root(index, offset) for index, offset in enumerate(representatives)
        )
        roots = tuple(result for result, _, _ in walks)
        union_sources: set[BoundaryChart] = set()
        union_keys: set[tuple[BoundaryChart, Scope]] = set()
        total_calls = total_leaves = total_unique = 0
        total_unique_keys = total_reused_keys = 0
        for result, sources, keys in walks:
            total_calls += result.recursive_calls
            total_leaves += result.terminal_leaves
            total_unique += result.unique_source_states
            total_unique_keys += result.unique_source_scope_pairs
            total_reused_keys += result.reused_source_scope_visits
            union_sources.update(sources)
            union_keys.update(keys)
        return {
            "scope": "bounded source-selected Compact B1 audit; not production",
            "roots": [result.as_json() for result in roots],
            "root_count": len(roots),
            "total_recursive_calls": total_calls,
            "total_terminal_leaves": total_leaves,
            "sum_unique_source_states": total_unique,
            "sum_unique_source_scope_pairs": total_unique_keys,
            "reused_source_scope_visits": total_reused_keys,
            "shared_unique_source_scope_pairs": len(union_keys),
            "cross_root_duplicate_source_scope_visits": (
                total_unique_keys - len(union_keys)
            ),
            "shared_unique_source_states": len(union_sources),
            "cross_root_duplicate_source_visits": total_unique - len(union_sources),
            "clock": "integer phase residue 0..923, grouped by exact core period",
        }
    if type(root_index) is not int or not 0 <= root_index < len(representatives):
        raise ValueError("root index must be in 0..45")
    result = audit_root(root_index, representatives[root_index])
    return {
        "scope": "bounded source-selected Compact B1 audit; not production",
        "authority": "shared entry_headroom/classify_near_port/chart_step arithmetic",
        "clock": "integer phase residue 0..923; no 924-bit masks or response rows",
        "source_graph": result.as_json(),
        "production_cutover": False,
        "semantic_warning": (
            "These counts audit the source-scope graph only. They do not prove "
            "weighted continuation equivalence or a source-only Moore quotient."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root", type=int, default=0, help="canonical root index 0..45"
    )
    parser.add_argument(
        "--all-roots",
        action="store_true",
        help="repeat the bounded walk for all 46 roots and report shared states",
    )
    args = parser.parse_args()
    print(
        json.dumps(
            audit_scope_graph(root_index=args.root, all_roots=args.all_roots), indent=2
        )
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
