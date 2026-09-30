"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Initial,
    Transfer,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryStateID,
    ImageBinding,
)
from number_compiler.resources.metric_records import LedgerMetrics
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.diamond_runtime import build

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.execution.continuations.diamond_context_program import (
        ContextObservation,
        ContextProgramArena,
    )
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def populated() -> tuple[
    DiamondRuntime, ActionProgramID, ContextProgramArena, ContextObservation
]:
    runtime, action = build(CollatzPhysicalBlockEffect(), (1, 0, 1, 1), 8, 2)
    identity = runtime.actions.identity
    left, right = (
        runtime.execute(Initial(identity, 0)),
        runtime.execute(Initial(identity, 1)),
    )
    assert isinstance(left, BoundaryStateID) and isinstance(right, BoundaryStateID)
    provider = ImageBinding(identity, runtime.cells.source(0, 3), left, right)
    incoming = runtime.execute(Initial(action, 0))
    assert isinstance(incoming, BoundaryStateID)
    runtime.execute(Transfer(provider, action, incoming, 0))
    contexts = runtime.pair_macros.contexts
    parent = next(
        request
        for request in contexts.observations
        if contexts.resolve(request.program).kind == "join"
    )
    return runtime, action, contexts, parent


def assert_context_inventory(
    contexts: ContextProgramArena, report: LedgerMetrics
) -> None:
    inventory = {row.owner: row for row in report.resource_inventory}
    assert inventory[contexts.observations.owner].observed_entries == len(
        contexts.observations
    )
    assert inventory[contexts.unary.owner].observed_entries == len(contexts.unary._memo)
