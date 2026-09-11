from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_interfaces import (
    HigherLocalInterfaceArena,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceForestID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.field_action import (
    ReverseActionAutomorphisms,
    ReverseFieldActionArena,
)
from number_compiler.sequences.reverse_add.higher_interface import (
    ReverseHigherInterfaceCompiler,
)
from number_compiler.sequences.reverse_add.higher_schema import (
    ReverseHigherActionSchema,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.continuations.higher_bimachine import (
        HigherBimachineRuntime,
    )
    from number_compiler.hashlife.execution.continuations.higher_interfaces import (
        HigherLocalInterfaceArena,
    )
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )
    from number_compiler.hashlife.execution.field_images import (
        SourceCellArena,
        SourceForestID,
    )
    from number_compiler.sequences.reverse_add.field_action import (
        ReverseFieldActionArena,
    )
    from number_compiler.sequences.reverse_add.higher_interface import (
        ReverseHigherInterfaceCompiler,
    )


def _join(before: object, after: object) -> object:
    assert type(before) is str and type(after) is str
    return before + after


def _fixture(
    source: tuple[int, ...] = (7, 18, 7, 19, 19, 19, 19, 19),
) -> tuple[
    ReverseFieldActionArena,
    FieldCellActionID,
    HigherSemanticArena,
    HigherBimachineRuntime,
    HigherLocalInterfaceArena,
    ReverseHigherInterfaceCompiler,
    SourceCellArena,
    SourceForestID,
]:
    ledger = ResourceLedger()
    geometry = SourceGeometry(
        ledger,
        ExactSource(source, 10, blank=19, extent=len(source), alphabet_size=20),
    )
    geometry.span(source, 19, len(source))
    sources = SourceCellArena(geometry)
    binding = sources.forest(0, len(source))
    actions = ReverseFieldActionArena(
        base=10,
        order=8,
        residual_identity="",
        output_identity="",
        residual_compose=_join,
        output_compose=_join,
        automorphisms=ReverseActionAutomorphisms.trivial(),
        ledger=ledger,
    )
    neutral = actions.intern_residual("")
    primitive = actions.intern(
        base=10,
        innovation=ReverseAddCyclotomicInnovationBlock.atom(
            (1,),
            0,
            order=8,
            bits=5,
        ),
        carry_forward=CarryFn.ID,
        carry_backward=CarryFn.ID,
        residual=actions.intern_residual("p"),
        output=actions.intern_output("p"),
        geometry=actions.resolve(actions.identity).geometry,
    )
    terminal = actions.intern(
        base=10,
        innovation=ReverseAddCyclotomicInnovationBlock.identity(order=8, bits=5),
        carry_forward=CarryFn.ID,
        carry_backward=CarryFn.ID,
        residual=neutral,
        output=actions.intern_output("terminal"),
        geometry=actions.resolve(actions.identity).geometry,
    )
    schema = ReverseHigherActionSchema(actions, primitive, terminal)
    semantics = HigherSemanticArena(schema)
    runtime = HigherBimachineRuntime(semantics, sources)
    interfaces = HigherLocalInterfaceArena(semantics)
    compiler = ReverseHigherInterfaceCompiler(
        actions,
        schema,
        semantics,
        runtime,
        interfaces,
    )
    return (
        actions,
        primitive,
        semantics,
        runtime,
        interfaces,
        compiler,
        sources,
        binding,
    )
