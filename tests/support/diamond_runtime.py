"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from collections.abc import Sequence
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def build(
    effect: BlockEffect, values: Sequence[int], length: int, exponent: int
) -> tuple[DiamondRuntime, ActionProgramID]:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    atom = compiler.atom(effect)
    geometry = SourceGeometry(
        ledger,
        ExactSource(
            tuple(values),
            effect.base,
            blank=effect.blank,
            extent=length,
            alphabet_size=effect.blank,
        ),
    )
    geometry.span(values, effect.blank, length)
    runtime = DiamondRuntime(compiler, geometry)
    action = runtime.actions.power(runtime.actions.intern(atom), exponent)
    return runtime, action


def oracle(
    effect: BlockEffect, values: Sequence[int], length: int, exponent: int
) -> list[int]:
    values = list(values) + [effect.blank] * (length - len(values))
    for _ in range(exponent):
        left = [effect.initial(BoundarySide.LEFT)]
        right = [effect.initial(BoundarySide.RIGHT)]
        for symbol in values:
            left.append(effect.advance(BoundarySide.LEFT, left[-1], symbol))
        for symbol in reversed(values):
            right.append(effect.advance(BoundarySide.RIGHT, right[-1], symbol))
        right.reverse()
        values = [
            effect.emit(left[i], value, right[i + 1]) for i, value in enumerate(values)
        ]
    return values
