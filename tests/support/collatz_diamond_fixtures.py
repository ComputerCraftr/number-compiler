"""Collatz-owned HashLife diamond fixtures for shared-algebra tests."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Initial,
    Transfer,
)
from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    CompilePrimitiveFunction,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryStateID,
    ImageBinding,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import StateSort
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.physical_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.sequences.collatz.tile_family_hooks import (
    collatz_tile_hooks,
    collatz_tile_hooks_for_effect,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import (
        ActionProgramID,
        TransferSummaryID,
    )
    from number_compiler.hashlife.execution.continuations.diamond_context_program import (
        ContextObservation,
        ContextProgramArena,
    )
    from number_compiler.hashlife.execution.tile_execution_adapter import (
        FamilyTileHooks,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import ExprID
    from number_compiler.hashlife.observation.diamond_query import (
        DiamondApplication,
    )


def collatz_continuation_runtime(
    effect: CollatzPhysicalBlockEffect | PhysicalCollatzFourBlockEffect | None = None,
) -> tuple[DiamondRuntime, ActionProgramID]:
    """Build the admitted Collatz source used by primitive-continuation tests."""
    ledger = ResourceLedger()
    actual_effect = CollatzPhysicalBlockEffect() if effect is None else effect
    compiler = LazyCompiler(
        ledger, family_hooks=collatz_tile_hooks_for_effect(actual_effect)
    )
    atom = compiler.atom(actual_effect)
    geometry = SourceGeometry(ledger, ExactSource((1, 1), 2, "collatz", 2, 8))
    geometry.span((1, 1), 2, 8)
    runtime = DiamondRuntime(compiler, geometry)
    action = runtime.actions.intern(atom)
    runtime.kernel(action)
    return runtime, action


def collatz_higher_context_runtime(
    bits: tuple[int, ...] = (1, 1, 0, 1, 1), extent: int = 8
) -> tuple[DiamondRuntime, ActionProgramID]:
    """Build the legacy-hook Collatz source used by higher-context tests."""
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger, family_hooks=collatz_tile_hooks())
    primitive = compiler.atom(CollatzPhysicalBlockEffect())
    geometry = SourceGeometry(ledger, ExactSource(bits, 2, "collatz", 2, extent))
    geometry.span(bits, 2, extent)
    runtime = DiamondRuntime(compiler, geometry)
    action = runtime.actions.intern(primitive)
    return runtime, action


def collatz_context_program_case() -> tuple[
    DiamondRuntime, ActionProgramID, ContextProgramArena, ContextObservation
]:
    """Build Collatz data for context-program ownership and cache tests."""
    runtime, action = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (1, 0, 1, 1), 8, 2
    )
    identity = runtime.actions.identity
    left, right = (
        runtime.execute(Initial(identity, 0)),
        runtime.execute(Initial(identity, 1)),
    )
    assert isinstance(left, BoundaryStateID) and isinstance(right, BoundaryStateID)
    provider = ImageBinding(identity, runtime.cells.source(0, 3), left, right)
    incoming = runtime.execute(Initial(action, 0))
    assert isinstance(incoming, BoundaryStateID)
    runtime.execute(Transfer(provider, action, incoming, 0))
    contexts = runtime.pair_macros.contexts
    parent = next(
        request
        for request in contexts.observations
        if contexts.resolve(request.program).kind == "join"
    )
    return runtime, action, contexts, parent


def collatz_continuation_payload_case() -> tuple[
    DiamondRuntime,
    ActionProgramID,
    ExprID,
    ExprID,
    CompilePrimitiveFunction,
    TransferSummaryID,
]:
    """Build the Collatz primitive-continuation payload used by audit tests."""
    runtime, action = collatz_higher_context_runtime()
    runtime.kernel(action)
    arena = runtime.higher.expressions
    variable = arena.variable(StateSort(action, 0), "primitive-input")
    expression = arena.primitive_advance(action, 0, variable, arena.symbol(action, 1))
    request = CompilePrimitiveFunction(variable, expression)
    function = runtime.execute(request)
    assert runtime.primitive_continuations.maps[request] == function
    return runtime, action, variable, expression, request, function


def _collatz_hooks(
    effect: CollatzPhysicalBlockEffect | PhysicalCollatzFourBlockEffect,
) -> FamilyTileHooks | None:
    if type(effect) not in (CollatzPhysicalBlockEffect, PhysicalCollatzFourBlockEffect):
        raise TypeError("Collatz diamond fixtures require an admitted Collatz effect")
    return collatz_tile_hooks_for_effect(effect)


def build_collatz_diamond_runtime(
    effect: CollatzPhysicalBlockEffect | PhysicalCollatzFourBlockEffect,
    values: tuple[int, ...],
    length: int,
    exponent: int,
) -> tuple[DiamondRuntime, ActionProgramID]:
    """Build a runtime with the Collatz-owned adapter explicitly attached."""
    from tests.support.diamond_runtime import build

    return build(effect, values, length, exponent, family_hooks=_collatz_hooks(effect))


def build_collatz_diamond_application(
    effect: CollatzPhysicalBlockEffect | PhysicalCollatzFourBlockEffect,
    source: tuple[int, ...],
    length: int,
    steps: int,
) -> DiamondApplication:
    """Build a query with the Collatz-owned adapter explicitly attached."""
    from tests.support.diamond_query import build

    return build(effect, source, length, steps, family_hooks=_collatz_hooks(effect))
