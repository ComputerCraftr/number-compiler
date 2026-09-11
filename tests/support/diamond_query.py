"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.observation.diamond_query import DiamondApplication
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.observation.diamond_query import DiamondApplication


def build(
    effect: BlockEffect, source: tuple[int, ...], length: int, steps: int
) -> DiamondApplication:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    atom = compiler.atom(effect)
    geometry = SourceGeometry(
        ledger,
        ExactSource(
            source,
            effect.base,
            blank=effect.blank,
            extent=length,
            alphabet_size=effect.blank,
        ),
    )
    geometry.span(source, effect.blank, length)
    runtime = DiamondRuntime(compiler, geometry)
    root = runtime.actions.power(runtime.actions.intern(atom), steps)
    return DiamondApplication(runtime, root)


def oracle(
    effect: BlockEffect, source: tuple[int, ...], length: int, steps: int
) -> list[int]:
    word = list(source) + [effect.blank] * (length - len(source))
    for _ in range(steps):
        left, right = (
            [effect.initial(BoundarySide.LEFT)],
            [effect.initial(BoundarySide.RIGHT)],
        )
        for symbol in word:
            left.append(effect.advance(BoundarySide.LEFT, left[-1], symbol))
        for symbol in reversed(word):
            right.append(effect.advance(BoundarySide.RIGHT, right[-1], symbol))
        right.reverse()
        word = [
            effect.emit(left[i], symbol, right[i + 1]) for i, symbol in enumerate(word)
        ]
    return word
