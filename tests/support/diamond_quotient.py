"""Publication tests distinguish complete semantic results from recipes."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import (
    ExactSource,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
from number_compiler.hashlife.actions.diamond_actions import (
    ImageCellArena,
    TemporalActionArena,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherEmit,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import Result, Task
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
from number_compiler.hashlife.interfaces.diamond_quotient import (
    DiamondQuotientArena,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    COMPONENT_ROLES,
    DiamondKey,
    LocalInterfaceID,
    MacroComponents,
    MacroInterface,
    StructureArena,
    StructureID,
)
from number_compiler.hashlife.observation.diamond_query import DiamondApplication
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.finite_function_types import (
        SemanticFunctionID,
    )
    from number_compiler.hashlife.actions.diamond_actions import (
        CellID,
        PortSignatureID,
    )


def setup_arena() -> tuple[
    ResourceLedger,
    SemanticFunctionArena,
    DiamondQuotientArena,
    ImageCellArena,
    FinitePort,
    PortSignatureID,
    MacroComponents,
    SemanticFunctionID,
    SemanticFunctionID,
    SemanticFunctionID,
]:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    cells = source_cells(ledger)
    arena = DiamondQuotientArena(functions, cells)
    port = FinitePort(PortVariable(0, 0, "carry", 0), 2)
    inputs = (port,)
    signature = FunctionSignature(inputs, BOOL)
    zero, one = functions.atom(signature, 0), functions.atom(signature, 1)
    variable = functions.variable(inputs, port, BOOL)
    interface = MacroInterface(
        SemanticIdentity("test-v1", ("complete-test-kernel",)),
        inputs,
        (BOOL,) * len(COMPONENT_ROLES),
        one,
    )
    declared = arena.intern_interface(interface)
    components = MacroComponents(*(zero for _ in COMPONENT_ROLES))
    return (
        ledger,
        functions,
        arena,
        cells,
        port,
        declared,
        components,
        zero,
        one,
        variable,
    )


def source_cells(ledger: ResourceLedger) -> ImageCellArena:
    source = SourceGeometry(ledger, ExactSource((1, 0), 2, blank=2, extent=2))
    source.span((1, 0), 2, 2)
    return ImageCellArena(TemporalActionArena(LazyCompiler(ledger)), source)


def parent_request(
    arena: DiamondQuotientArena,
    cells: ImageCellArena,
    signature: PortSignatureID,
    components: MacroComponents,
) -> tuple[LocalInterfaceID, CellID, DiamondKey]:
    quotient = arena.intern(signature, components)
    cell = cells.source_span(0, 2)[0][1]
    return quotient, cell, DiamondKey(quotient, quotient, cell, 1, 0, 0, signature)


def restricted_setup() -> tuple[
    ResourceLedger,
    DiamondQuotientArena,
    PortSignatureID,
    MacroComponents,
    MacroComponents,
]:
    ledger, functions, arena, _, _, signature, components, zero, one, variable = (
        setup_arena()
    )
    allowed = functions.ite(variable, zero, one)
    restricted = arena.intern_interface(
        replace(arena.interface(signature), admissible=allowed)
    )
    return ledger, arena, restricted, components, replace(components, output=variable)


def zero_atoms(arena: DiamondQuotientArena, port: FinitePort) -> MacroComponents:
    bit = arena.structures.bits.constant(FunctionSignature((port,), BOOL), 0)
    atom = arena.structures.atom(bit)
    return MacroComponents(*(atom for _ in COMPONENT_ROLES))


def capture_root_emissions(
    app: DiamondApplication, monkeypatch: pytest.MonkeyPatch
) -> list[ExprID]:
    """Record exactly the observed root emissions without replacing evaluation."""
    outputs: list[ExprID] = []
    execute = app.runtime.execute

    def observe(task: Task) -> Result:
        result = execute(task)
        if type(task) is HigherEmit and task.action == app.root:
            assert isinstance(result, ExprID)
            outputs.append(result)
        return result

    monkeypatch.setattr(app.runtime, "execute", observe)
    return outputs


def warmed_neighbor_application() -> DiamondApplication:
    from tests.support.diamond_observation_adversarial import neighbor_xor
    from tests.support.diamond_query import build

    app = build(neighbor_xor(), (0, 1), 4, 1)
    app.runtime.kernels.intern(app.runtime.actions.primitive(app.root))
    return app


def division_interface(
    projection: LazyProjection,
) -> tuple[
    PrimitiveTileKernelAdapter,
    FieldCellActionID,
    LocalInterfaceID,
    DiamondQuotientArena,
]:
    adapter = projection.scheduler.adapter
    assert type(adapter) is PrimitiveTileKernelAdapter
    action = adapter.admit(SymbolicBinaryDivisionEffect(257), cocycle=TemporalCocycle())
    interface = adapter.compile_interface(
        action, projection._application.source, adapter.wiring(action)
    )
    return adapter, action, interface, projection.scheduler.results.interfaces


def curried_increment(
    structures: StructureArena, x: FinitePort, y: FinitePort, word: AtomSort
) -> StructureID:
    bits = structures.bits
    left = bits.variable((x, y), x, word)
    right = bits.variable((x, y), y, BOOL)
    return structures.curry(structures.atom(bits.add(left, right, word)), (y,))
