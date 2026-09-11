"""Fresh diamond test helpers extracted without changing their execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.diamond_actions import (
    ImageCellArena,
    TemporalActionArena,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.actions.diamond_actions import (
        ImageCellArena,
        TemporalActionArena,
    )
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
    from number_compiler.resources.ledger import ResourceLedger


def arenas(
    length: int = 16,
) -> tuple[
    ResourceLedger,
    LazyCompiler,
    TemporalActionArena,
    ImageCellArena,
    ActionProgramID,
    ActionProgramID,
]:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    base = compiler.atom(BaseBlockEffect(10))
    terminal = compiler.atom(DigitNormalizeBlockEffect(10))
    actions = TemporalActionArena(compiler)
    first, second = actions.intern(base), actions.intern(terminal)
    geometry = SourceGeometry(
        ledger, ExactSource((7, 18, 7), 10, "reverse-add", 19, length, alphabet_size=19)
    )
    geometry.span((7, 18, 7), 19, length)
    cells = ImageCellArena(actions, geometry)
    return ledger, compiler, actions, cells, first, second
