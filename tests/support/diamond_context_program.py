"""Generic inventory assertions for finite context-program stores."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.resources.metric_records import LedgerMetrics

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_context_program import (
        ContextProgramArena,
    )


def assert_context_inventory(
    contexts: ContextProgramArena, report: LedgerMetrics
) -> None:
    inventory = {row.owner: row for row in report.resource_inventory}
    assert inventory[contexts.observations.owner].observed_entries == len(
        contexts.observations
    )
    assert inventory[contexts.unary.owner].observed_entries == len(
        contexts.unary.audit_snapshot().container
    )
