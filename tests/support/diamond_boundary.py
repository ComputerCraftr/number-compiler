"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryActionArena,
    BoundaryStateID,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from tests.support.diamond_actions import arenas

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.actions.diamond_actions import (
        ImageCellArena,
        TemporalActionArena,
    )
    from number_compiler.resources.ledger import ResourceLedger


def boundary() -> tuple[
    ResourceLedger,
    TemporalActionArena,
    ImageCellArena,
    BoundaryActionArena,
    ActionProgramID,
    ActionProgramID,
]:
    ledger, _, actions, cells, first, second = arenas()
    kernels = DiamondKernelArena(ledger)
    kernels.intern(actions.primitive(first))
    kernels.intern(actions.primitive(second))
    result = BoundaryActionArena(actions, kernels, cells)
    return ledger, actions, cells, result, first, second


def composed_anchor(
    actions: TemporalActionArena,
    arena: BoundaryActionArena,
    first: ActionProgramID,
    second: ActionProgramID,
) -> tuple[ActionProgramID, BoundaryStateID]:
    return actions.compose(first, second), arena.literal(first, 0, 0)
