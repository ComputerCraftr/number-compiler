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
from number_compiler.sequences.collatz.tile_family_hooks import (
    collatz_tile_hooks_for_effect,
)
from tests.support.semantic_oracles import scan_ports

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID


def build(
    effect: BlockEffect, values: Sequence[int], length: int, exponent: int
) -> tuple[DiamondRuntime, ActionProgramID]:
    ledger = ResourceLedger()
    hooks = collatz_tile_hooks_for_effect(effect)
    compiler = LazyCompiler(ledger, family_hooks=hooks)
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
        _, _, values = scan_ports(
            effect,
            values,
            effect.initial(BoundarySide.LEFT),
            effect.initial(BoundarySide.RIGHT),
        )
    return values
