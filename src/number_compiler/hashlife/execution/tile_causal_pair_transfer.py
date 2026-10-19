"""Dispatch an optional family-owned finite pair transfer."""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
    from number_compiler.resources.causal_types import CausalPrefix, CausalState


def finite_pair_transfer(
    engine: CausalTileEngine,
    action: FieldCellActionID,
    side: int,
    prefix: CausalPrefix,
    opposite: CausalState,
    consumer: CausalState,
) -> int | None:
    """Use only a runtime-injected family strategy; shared code has no law.

    Returning ``None`` declines the optimization and leaves the canonical
    causal scheduler's general recurrence in control.
    """
    strategy = engine.adapter.pair_transfer
    if strategy is None:
        return None
    result = strategy.transfer(engine, action, side, prefix, opposite, consumer)
    if result is not None and type(result) is not int:
        raise TypeError("finite pair transfer returned a noninteger boundary state")
    return result


__all__ = ["finite_pair_transfer"]
