"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from tests.support.diamond_observation_adversarial import neighbor_xor
from tests.support.diamond_query import build

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def machine(
    effect: BlockEffect | None = None,
) -> tuple[DiamondRuntime, ActionProgramID]:
    app = build(neighbor_xor() if effect is None else effect, (0, 1, 1, 0), 8, 1)
    app.runtime.kernel(app.root)
    return app.runtime, app.root
