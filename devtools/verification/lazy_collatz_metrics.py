"""Read-only metric collection for the lazy Collatz application."""

from __future__ import annotations

from typing import Protocol

from number_compiler.resources.ledger import ResourceLedger


class LazyCollatzMetricsSource(Protocol):
    """The narrow counters and retained stores used by the metrics report."""

    @property
    def program_compositions(self) -> int: ...

    @property
    def applications(self) -> int: ...

    @property
    def branch_evaluations(self) -> int: ...

    @property
    def carry_cell_evaluations(self) -> int: ...

    @property
    def maximum_carry(self) -> int: ...

    @property
    def point_queries(self) -> int: ...

    @property
    def fixed_cycle_skips(self) -> int: ...

    @property
    def summary_queries(self) -> int: ...

    @property
    def source_transfer_compositions(self) -> int: ...

    @property
    def ledger(self) -> ResourceLedger: ...

    def retained_entries(self) -> int: ...


def collect_lazy_collatz_metrics(
    application: LazyCollatzMetricsSource,
    *,
    program_entries: int,
    summary_entries: int,
) -> dict[str, int]:
    """Report the application's existing counters without creating state."""
    return {
        "macro_actions": program_entries,
        "macro_compositions": application.program_compositions,
        "macro_applications": application.applications,
        "nonlinear_branch_evaluations": application.branch_evaluations,
        "exact_endpoint_entries": 0,
        "summary_entries": summary_entries,
        "carry_cell_evaluations": application.carry_cell_evaluations,
        "maximum_carry": application.maximum_carry,
        "point_queries": application.point_queries,
        "fixed_cycle_skips": application.fixed_cycle_skips,
        "retained_entries": application.retained_entries(),
        "source_entries": 1,
        "summary_queries": application.summary_queries,
        "source_transfer_compositions": application.source_transfer_compositions,
        "symbolic_port_queries": application.ledger.counters.get(
            "symbolic_port_queries", 0
        ),
        "symbolic_maximum_port_bits": application.ledger.counters.get(
            "symbolic_maximum_port_bits", 0
        ),
    }
