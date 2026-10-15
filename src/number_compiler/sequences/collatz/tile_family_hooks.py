"""Explicit HashLife hooks for the physical Collatz tile family."""

from __future__ import annotations

from dataclasses import replace
from threading import Lock
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.execution.tile_execution_adapter import FamilyTileHooks
from number_compiler.hashlife.interfaces.tile_interface_compilation import (
    validate_symbol_observation_context,
)
from number_compiler.hashlife.tiles.ordered_boolean_support import (
    OrderedBooleanSupport,
)
from number_compiler.hashlife.tiles.temporal_cocycle import TemporalCocycle
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.diamond_cycle import (
    PhysicalCycleProjection,
    cycle_active_width,
    cycle_point,
    physical_cycle,
    validate_physical_cycle,
)
from number_compiler.sequences.collatz.physical_support import (
    PhysicalSupport,
    PhysicalSupportArena,
)
from number_compiler.sequences.collatz.tile_cycle import complete_collatz_cycle
from number_compiler.sequences.collatz.tile_root import initial_event_shift
from number_compiler.sequences.collatz.tile_root_completion import (
    complete_collatz_root,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.block_effect import BlockEffect
    from number_compiler.arithmetic.functions.finite_function_types import (
        AtomSort,
        FinitePort,
    )
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
    from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
    from number_compiler.hashlife.tiles.tile_results import ResultLease
    from number_compiler.hashlife.tiles.tiles import TileID
    from number_compiler.resources.ledger import ResourceLedger


def _make_support_arena(
    max_nodes: int,
    ledger: ResourceLedger,
) -> PhysicalSupportArena:
    return PhysicalSupportArena(max_nodes=max_nodes, ledger=ledger)


def _primitive_support(
    scheduler: TileScheduler,
    action: FieldCellActionID,
    source: TileID,
    ports: tuple[int, ...],
) -> PhysicalSupport | None:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        return None
    record = adapter._action(action)
    if record.children is not None:
        return None
    kernel = adapter.kernels.kernel(record.kernel)
    if type(kernel.effect) is not CollatzPhysicalBlockEffect:
        return None
    if len(ports) != 2:
        raise ValueError("physical support requires two admitted boundary ports")
    symbol = scheduler.tiles.resolve(source).symbol
    support_arena = _physical_support_arena(scheduler)
    if ports[0] != kernel.initial(BoundarySide.LEFT) or symbol not in (0, 1):
        return _require_physical_support(support_arena.identity)
    return _require_physical_support(
        support_arena.odd if symbol else support_arena.even
    )


def _physical_support_arena(scheduler: TileScheduler) -> PhysicalSupportArena:
    arena = scheduler.physical_supports
    if type(arena) is not PhysicalSupportArena:
        raise TypeError("Collatz support operation requires its exact support arena")
    return arena


def _require_physical_support(value: OrderedBooleanSupport) -> PhysicalSupport:
    if type(value) is not PhysicalSupport:
        raise TypeError("Collatz support arena returned a foreign node type")
    return value


def _clone_effect(effect: BlockEffect) -> BlockEffect:
    if type(effect) is not CollatzPhysicalBlockEffect:
        raise TypeError("Collatz tile hooks received a foreign effect")
    return CollatzPhysicalBlockEffect()


def _lower_compatibility(
    effect: BlockEffect,
    compiler: LazyCompiler,
) -> BlockEffect:
    from number_compiler.sequences.collatz.compilation import (
        compile_collatz_physical_power,
    )
    from number_compiler.sequences.collatz.physical_kernel import (
        PhysicalCollatzFourBlockEffect,
    )

    if type(effect) is not PhysicalCollatzFourBlockEffect:
        raise TypeError("Collatz compatibility lowering received a foreign effect")
    effect.validate()
    lowered = compile_collatz_physical_power(compiler, 4).root
    if lowered is None or lowered.exponent != effect.exponent:
        raise AssertionError("fixed physical action lost its four-step span")
    return lowered


def _validate_compatibility(effect: BlockEffect) -> None:
    from number_compiler.sequences.collatz.physical_kernel import (
        PhysicalCollatzFourBlockEffect,
    )

    if type(effect) is not PhysicalCollatzFourBlockEffect:
        raise TypeError("Collatz compatibility validator received a foreign effect")
    effect.validate()


def _compatibility_right_halo(effect: BlockEffect) -> int:
    del effect
    return 4


def _compatibility_right_reset_radius(effect: BlockEffect) -> int:
    del effect
    return 4


def _compatibility_tile_admission_error(effect: BlockEffect) -> str:
    from number_compiler.sequences.collatz.physical_kernel import (
        PhysicalCollatzFourBlockEffect,
    )

    if type(effect) is not PhysicalCollatzFourBlockEffect:
        raise TypeError("Collatz tile rejection received another compatibility type")
    return "unsupported weighted runtime kernel: no certified odd-event output channel"


def _admits_source_profile(runtime: DiamondRuntime, action: ActionProgramID) -> bool:
    from number_compiler.sequences.collatz.physical_kernel import (
        PhysicalCollatzFourBlockEffect,
    )

    node = runtime.actions.resolve(action)
    if node.kind != "compose":
        return False
    for child in (node.first, node.second):
        reference = runtime.actions.reference(child)
        if runtime.actions.resolve(reference).kind != "atom":
            return False
        effect = runtime.actions.primitive(reference)
        if type(effect) is not PhysicalCollatzFourBlockEffect:
            return False
        effect.validate()
    return True


def _make_source_profile(
    runtime: DiamondRuntime,
    action: ActionProgramID,
) -> object:
    from number_compiler.sequences.collatz.physical_pair_certificate import (
        load_verified_c4_pair_left,
    )

    del runtime, action
    return load_verified_c4_pair_left()


def _certified_program_leaf(effect: BlockEffect) -> tuple[int, int] | None:
    if type(effect) is CollatzPhysicalBlockEffect:
        return (1, 0)
    return None


def _certified_compatibility_program_leaf(
    effect: BlockEffect,
) -> tuple[int, int] | None:
    if type(effect) is CollatzPhysicalBlockEffect:
        return (1, 0)
    from number_compiler.sequences.collatz.physical_kernel import (
        PhysicalCollatzFourBlockEffect,
    )

    if type(effect) is PhysicalCollatzFourBlockEffect:
        effect.validate()
        return (4, 0)
    return None


def _complete_clock(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    whole_output: bool,
) -> ResultLease | None:
    result = complete_collatz_cycle(scheduler, key)
    if result is not None or not whole_output:
        return result
    return complete_collatz_root(scheduler, key)


def _observe_primitive(
    kernel: PrimitiveKernel,
    left_state: int,
    symbol: int,
    right_state: int,
) -> tuple[int, ...]:
    kernel._check(left_state, kernel.left_count)
    kernel._check(right_state, kernel.right_count)
    kernel._check(symbol, kernel.blank + 1)
    behavior = kernel.behavior
    if behavior is not None:
        return behavior.observation(
            behavior.left_classes[left_state],
            symbol,
            behavior.right_classes[right_state],
        )
    odd_event = int(
        type(kernel.effect) is CollatzPhysicalBlockEffect
        and left_state == kernel.initial(BoundarySide.LEFT)
        and symbol == 1
    )
    return odd_event, 0, 0


def _observe_source_tile(
    scheduler: TileScheduler,
    action: FieldCellActionID,
    source: TileID,
    left_state: int,
    right_state: int,
) -> tuple[TemporalCocycle, OrderedBooleanSupport | None]:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        raise TypeError("physical source observation requires the canonical adapter")
    record = adapter._action(action)
    if record.children is not None:
        raise ValueError("source-tile observation requires a primitive action")
    kernel = adapter.kernels.kernel(record.kernel)
    if type(kernel.effect) is not CollatzPhysicalBlockEffect:
        raise ValueError("physical source observation received another law")
    kernel._check(left_state, kernel.left_count)
    kernel._check(right_state, kernel.right_count)
    arena = _physical_support_arena(scheduler)
    if left_state != kernel.initial(BoundarySide.LEFT):
        scheduler.ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_EVENT_SOURCE_READS_ELIDED)
        return TemporalCocycle(), arena.identity
    symbol = scheduler.tiles.point(source, 0)
    odd = int(symbol == 1)
    return TemporalCocycle(event_weight=odd), arena.odd if odd else arena.even


def _support_symbol(
    scheduler: TileScheduler,
    action: FieldCellActionID,
    symbol: int,
    ports: tuple[int, ...],
) -> OrderedBooleanSupport | None:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    adapter = scheduler.adapter
    if type(adapter) is not PrimitiveTileKernelAdapter:
        raise TypeError("physical symbol support requires the canonical adapter")
    record = adapter._action(action)
    if record.children is not None:
        raise ValueError("symbol support requires a primitive action")
    kernel = adapter.kernels.kernel(record.kernel)
    if type(kernel.effect) is not CollatzPhysicalBlockEffect:
        return None
    if len(ports) != 2:
        raise ValueError("symbol support requires two admitted boundary ports")
    arena = _physical_support_arena(scheduler)
    if ports[0] != kernel.initial(BoundarySide.LEFT):
        return arena.identity
    if type(symbol) is not int or symbol not in (0, 1):
        raise ValueError("physical symbol support requires a binary digit")
    return arena.odd if symbol else arena.even


def _observe_symbol(
    adapter: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    symbol: int,
    interface: object,
    ports: tuple[int, ...],
) -> TemporalCocycle:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter as PrimitiveAdapter,
    )

    if type(adapter) is not PrimitiveAdapter:
        raise TypeError("physical Collatz observation requires the canonical adapter")
    kernel = validate_symbol_observation_context(
        adapter, action, symbol, interface, ports
    )
    if type(kernel.effect) is not CollatzPhysicalBlockEffect:
        return TemporalCocycle()
    odd = int(ports[0] == kernel.initial(BoundarySide.LEFT) and symbol == 1)
    return TemporalCocycle(0, odd, 0)


def _compile_leaf_output(
    adapter: PrimitiveTileKernelAdapter,
    kernel: PrimitiveKernel,
    symbol: int,
    ports: tuple[FinitePort, ...],
    left_port: FinitePort,
    right_port: FinitePort,
    output_sort: AtomSort,
) -> FactoredFunctionID:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter as PrimitiveAdapter,
    )
    from number_compiler.sequences.collatz.physical_output_quotient import (
        collatz_physical_leaf_output,
    )

    if type(adapter) is not PrimitiveAdapter:
        raise TypeError("physical Collatz output requires the canonical adapter")
    if type(kernel.effect) is not CollatzPhysicalBlockEffect:
        raise ValueError("physical Collatz output requires its primitive kernel")
    return collatz_physical_leaf_output(
        adapter.bits,
        kernel,
        symbol,
        ports,
        left_port,
        right_port,
        output_sort,
    )


_COLLATZ_TILE_HOOKS = FamilyTileHooks(
    effect_type=CollatzPhysicalBlockEffect,
    compatibility_type=None,
    clone_effect=_clone_effect,
    lower_compatibility_effect=None,
    validate_compatibility_effect=None,
    compatibility_right_halo=None,
    compatibility_right_reset_radius=None,
    source_profile_type=None,
    validate_source_profile_action=None,
    make_source_profile=None,
    certified_program_leaf=_certified_program_leaf,
    cycle_projection_type=PhysicalCycleProjection,
    make_cycle_projection=physical_cycle,
    validate_cycle_projection=validate_physical_cycle,
    project_cycle_point=cycle_point,
    project_cycle_width=cycle_active_width,
    spatial_events_add=True,
    make_support_arena=_make_support_arena,
    primitive_support=_primitive_support,
    complete_clock=_complete_clock,
    initial_event_shift=initial_event_shift,
    observe_primitive=_observe_primitive,
    observe_source_tile=_observe_source_tile,
    support_symbol=_support_symbol,
    observe_symbol=_observe_symbol,
    compile_leaf_output=_compile_leaf_output,
)
_COLLATZ_COMPATIBILITY_HOOKS: FamilyTileHooks | None = None
_COLLATZ_COMPATIBILITY_HOOKS_LOCK = Lock()


def collatz_runtime_tile_hooks() -> FamilyTileHooks:
    """Return the lightweight production hooks for primitive Collatz actions."""
    return _COLLATZ_TILE_HOOKS


def is_collatz_tile_hooks(hooks: object) -> bool:
    """Recognize only the canonical primitive or compatibility hook instance."""
    return hooks is _COLLATZ_TILE_HOOKS or (
        _COLLATZ_COMPATIBILITY_HOOKS is not None
        and hooks is _COLLATZ_COMPATIBILITY_HOOKS
    )


def _compatibility_tile_hooks() -> FamilyTileHooks:
    global _COLLATZ_COMPATIBILITY_HOOKS

    from number_compiler.sequences.collatz.physical_kernel import (
        PhysicalCollatzFourBlockEffect,
    )
    from number_compiler.sequences.collatz.physical_pair_certificate import (
        C4PairLeftCertificate,
    )

    if _COLLATZ_COMPATIBILITY_HOOKS is None:
        with _COLLATZ_COMPATIBILITY_HOOKS_LOCK:
            if _COLLATZ_COMPATIBILITY_HOOKS is None:
                _COLLATZ_COMPATIBILITY_HOOKS = replace(
                    _COLLATZ_TILE_HOOKS,
                    compatibility_type=PhysicalCollatzFourBlockEffect,
                    lower_compatibility_effect=_lower_compatibility,
                    validate_compatibility_effect=_validate_compatibility,
                    compatibility_right_halo=_compatibility_right_halo,
                    compatibility_right_reset_radius=(
                        _compatibility_right_reset_radius
                    ),
                    compatibility_tile_admission_error=(
                        _compatibility_tile_admission_error
                    ),
                    source_profile_type=C4PairLeftCertificate,
                    validate_source_profile_action=_admits_source_profile,
                    make_source_profile=_make_source_profile,
                    certified_program_leaf=_certified_compatibility_program_leaf,
                )
    return _COLLATZ_COMPATIBILITY_HOOKS


def collatz_compatibility_tile_hooks(effect: object) -> FamilyTileHooks:
    """Return C4 compatibility hooks only for an explicitly requested C4 effect."""
    from number_compiler.sequences.collatz.physical_kernel import (
        PhysicalCollatzFourBlockEffect,
    )

    if type(effect) is not PhysicalCollatzFourBlockEffect:
        raise TypeError("C4 compatibility hooks require the exact fixed effect")
    return _compatibility_tile_hooks()


def collatz_tile_hooks() -> FamilyTileHooks:
    """Return the legacy full Collatz hook set for explicit compatibility clients."""
    return _compatibility_tile_hooks()


def collatz_tile_hooks_for_effect(effect: object) -> FamilyTileHooks | None:
    """Select the ordinary or compatibility adapter from an exact effect."""
    if type(effect) is CollatzPhysicalBlockEffect:
        return collatz_runtime_tile_hooks()
    from number_compiler.sequences.collatz.physical_kernel import (
        PhysicalCollatzFourBlockEffect,
    )

    if type(effect) is PhysicalCollatzFourBlockEffect:
        return collatz_compatibility_tile_hooks(effect)
    return None


__all__ = [
    "collatz_compatibility_tile_hooks",
    "collatz_runtime_tile_hooks",
    "collatz_tile_hooks",
    "collatz_tile_hooks_for_effect",
    "is_collatz_tile_hooks",
]
