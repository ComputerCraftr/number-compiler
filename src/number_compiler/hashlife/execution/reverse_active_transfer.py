"""Consume a bound reverse output through a certified primitive action."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )


def consume_reverse_bound_output(
    adapter: PrimitiveTileKernelAdapter,
    consumer: FieldCellActionID,
    side: int,
    state: int,
    output: ReverseBoundOutput | None,
) -> int | None:
    """Return a primitive consumer exit, declining unsupported action profiles.

    Composite consumers require a separately certified successor-closed
    behavior transition. Treating their ``CausalPrefix`` as an integer would
    discard the explicit temporal edge, so this helper deliberately declines.
    """
    if output is None or adapter.action_children(consumer) is not None:
        adapter.ledger.bump(_execution_keys.REVERSE_ACTIVE_TRANSFER_DECLINES)
        return None
    law = adapter.primitive_law(consumer)
    if law.base != output.left.base or type(law.effect) not in (
        BaseBlockEffect,
        DigitNormalizeBlockEffect,
    ):
        adapter.ledger.bump(_execution_keys.REVERSE_ACTIVE_TRANSFER_DECLINES)
        return None
    if type(state) is not int:
        raise TypeError("primitive reverse consumer requires an exact finite state")
    result = (
        output.apply_digit_normalize(side, state)
        if type(law.effect) is DigitNormalizeBlockEffect
        else output.apply(side, state)
    )
    adapter.ledger.bump(_execution_keys.REVERSE_ACTIVE_TRANSFER_EVALUATIONS)
    return result


__all__ = ["consume_reverse_bound_output"]
