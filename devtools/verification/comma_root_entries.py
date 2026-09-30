"""Finite 91-entry cross-check, separate from global Isabelle admission.

The executable chart and least-rank computation reproduce the proposed root
boundary. This module supplies no runtime certificate or infinite-path theorem.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.verification.comma_semantic_quotients import (
    CommaFutureGraph,
    future_losing_ranks,
)
from number_compiler.sequences.comma.boundary_chart import (
    MAX_CHART_MOVES,
    PERIOD,
    BoundaryChart,
    chart_step,
)
from number_compiler.sequences.comma.boundary_quotient import BoundaryState


@dataclass(frozen=True, slots=True)
class CommaRootEntry:
    offset: int
    exponent_gain: int
    fork_a: int | None
    child_ranks: tuple[int | None, int | None] | None
    chart_visits: int

    @property
    def future_open(self) -> bool:
        return self.child_ranks is not None and None in self.child_ranks


def audit_root_entries(graph: CommaFutureGraph) -> tuple[CommaRootEntry, ...]:
    """Check every possible first crossing of 10**5, including all alternatives.

    Exhausting the existing chart guard is an error, never a losing verdict.
    The result retains rank evidence for both children, not a greedy choice.
    """
    ranks = future_losing_ranks(graph)
    indices = {state: index for index, state in enumerate(graph.states)}
    rows: list[CommaRootEntry] = []
    for offset in range(91):
        chart = BoundaryChart("entry", 1, 0, offset)
        for visits in range(1, MAX_CHART_MOVES + 1):
            move = chart_step(5, chart)
            if move.next_chart is not None:
                chart = move.next_chart
                continue
            children = None
            if move.fork_a is not None:
                phase = (5 + chart.delta) % PERIOD
                children = (
                    ranks[indices[BoundaryState("N", move.fork_a, phase)]],
                    ranks[indices[BoundaryState("Z", move.fork_a, phase)]],
                )
            rows.append(
                CommaRootEntry(offset, chart.delta, move.fork_a, children, visits)
            )
            break
        else:
            raise ValueError(f"comma entry {offset} exceeded the chart work bound")
    return tuple(rows)
