"""Reverse field action with one canonical implementation owner."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.field_action import (
    ReverseActionAutomorphisms,
    ReverseFieldActionArena,
    ReverseGeometry,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.field_images import (
        SourceCellID,
    )


def source_cells(
    values: tuple[int, ...], base: int = 10
) -> tuple[ResourceLedger, SourceCellArena, SourceCellID]:
    ledger = ResourceLedger()
    width = len(values)
    assert width and width & (width - 1) == 0
    geometry = SourceGeometry(
        ledger,
        ExactSource(
            values, base, blank=2 * base - 1, extent=width, alphabet_size=2 * base
        ),
    )
    geometry.span(values, 2 * base - 1, width)
    cells = SourceCellArena(geometry)
    return ledger, cells, cells.intern(0, width.bit_length() - 1)


def concatenate(before: object, after: object) -> object:
    assert isinstance(before, str) and isinstance(after, str)
    return before + after


def reverse_action_arena(
    *, ledger: ResourceLedger | None = None
) -> ReverseFieldActionArena:
    return ReverseFieldActionArena(
        base=10,
        order=8,
        residual_identity="",
        output_identity="",
        residual_compose=concatenate,
        output_compose=concatenate,
        automorphisms=ReverseActionAutomorphisms.trivial(),
        ledger=ledger,
    )


_DEFAULT_REVERSE_GEOMETRY = ReverseGeometry(0)


def reverse_action_atom(
    arena: ReverseFieldActionArena,
    name: str,
    *,
    growth: int,
    forward: CarryFn,
    backward: CarryFn,
    geometry: ReverseGeometry = _DEFAULT_REVERSE_GEOMETRY,
) -> FieldCellActionID:
    return arena.intern(
        base=10,
        innovation=ReverseAddCyclotomicInnovationBlock.atom(
            (ord(name),),
            growth,
            order=8,
            bits=5,
        ),
        carry_forward=forward,
        carry_backward=backward,
        residual=arena.intern_residual(name),
        output=arena.intern_output(name),
        geometry=geometry,
    )
