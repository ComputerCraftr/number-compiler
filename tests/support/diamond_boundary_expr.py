"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
)
from tests.support.diamond_boundary import boundary

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.actions.diamond_actions import TemporalActionArena
    from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryActionArena
    from number_compiler.resources.ledger import ResourceLedger


def context() -> tuple[
    ResourceLedger,
    TemporalActionArena,
    BoundaryActionArena,
    BoundaryExpressionArena,
    ActionProgramID,
    ActionProgramID,
]:
    ledger, actions, _, boundaries, first, second = boundary()
    expressions = BoundaryExpressionArena(boundaries)
    return ledger, actions, boundaries, expressions, first, second
