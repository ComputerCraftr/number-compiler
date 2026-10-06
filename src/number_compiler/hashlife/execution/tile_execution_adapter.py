"""Fixed execution-family interface consumed by the shared tile scheduler."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING, Protocol

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, _effect_key
from number_compiler.hashlife.tiles.ordered_boolean_support import (
    OrderedBooleanSupport,
    OrderedBooleanSupportArena,
)
from number_compiler.hashlife.tiles.temporal_cocycle import TemporalCocycle

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.arithmetic.functions.finite_function_types import (
        AtomSort,
        FinitePort,
    )
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
    from number_compiler.hashlife.execution.tile_causal_tasks import CausalPrefix
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
    from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
    from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
    from number_compiler.hashlife.tiles.tile_context import (
        ChildContext,
        PrimitiveTileResult,
        ResultSemantics,
    )
    from number_compiler.hashlife.tiles.tile_ports import ResultWiring
    from number_compiler.hashlife.tiles.tile_result_records import (
        CompletedResult,
        PoweredResultKey,
    )
    from number_compiler.hashlife.tiles.tile_results import ResultLease
    from number_compiler.hashlife.tiles.tiles import TileID
    from number_compiler.resources.ledger import ResourceLedger


class FinitePairTransfer(ABC):
    """Explicit runtime extension for one family-owned finite pair transfer.

    The shared causal driver knows only this bounded contract. Family-specific
    finite morphisms, alphabets and carry laws live behind the injected object.
    Instances belong to one scheduler ledger and clear source-bound bindings
    when a causal query releases its workspace.
    """

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger

    @abstractmethod
    def transfer(
        self,
        engine: CausalTileEngine,
        action: FieldCellActionID,
        side: int,
        prefix: CausalPrefix,
        opposite: object,
        consumer: object,
    ) -> int | None:
        """Consume an admitted primitive pair or decline it with ``None``."""

    @abstractmethod
    def clear_bindings(self) -> None:
        """Release query-bound source references after the driver completes."""


class FinitePairTransferFactory(ABC):
    """Create one family transfer instance for a canonical tile runtime."""

    @abstractmethod
    def create(self, ledger: ResourceLedger) -> FinitePairTransfer:
        """Create a ledger-owned transfer adapter."""


@dataclass(frozen=True, slots=True)
class FamilyTileHooks:
    """Explicit, typed extension supplied by a sequence-family owner.

    The shared scheduler never discovers family behavior from attribute names
    or imports a sequence package.  A family passes this record at the runtime
    boundary; the exact effect type and cloned result are checked before the
    shared kernel accepts them.
    """

    effect_type: type[BlockEffect]
    compatibility_type: type[BlockEffect] | None
    clone_effect: Callable[[BlockEffect], BlockEffect]
    lower_compatibility_effect: (
        Callable[[BlockEffect, LazyCompiler], BlockEffect] | None
    )
    validate_compatibility_effect: Callable[[BlockEffect], None] | None
    compatibility_right_halo: Callable[[BlockEffect], int | None] | None
    compatibility_right_reset_radius: Callable[[BlockEffect], int | None] | None
    source_profile_type: type[object] | None
    validate_source_profile_action: (
        Callable[[DiamondRuntime, ActionProgramID], bool] | None
    )
    make_source_profile: Callable[[DiamondRuntime, ActionProgramID], object] | None
    certified_program_leaf: Callable[[BlockEffect], tuple[int, int] | None] | None
    cycle_projection_type: type[object] | None
    make_cycle_projection: (
        Callable[[DiamondRuntime, ActionProgramID], object | None] | None
    )
    validate_cycle_projection: (
        Callable[[DiamondRuntime, ActionProgramID, object], bool] | None
    )
    project_cycle_point: Callable[[object, int], int] | None
    project_cycle_width: Callable[[object, int | None], int] | None
    spatial_events_add: bool
    make_support_arena: Callable[[int, ResourceLedger], OrderedBooleanSupportArena]
    primitive_support: Callable[
        [TileScheduler, FieldCellActionID, TileID, tuple[int, ...]],
        OrderedBooleanSupport | None,
    ]
    complete_clock: Callable[
        [TileScheduler, PoweredResultKey, bool], ResultLease | None
    ]
    initial_event_shift: Callable[
        [TileScheduler, PoweredResultKey], tuple[FieldCellActionID, int] | None
    ]
    observe_primitive: Callable[[PrimitiveKernel, int, int, int], tuple[int, ...]]
    observe_source_tile: Callable[
        [TileScheduler, FieldCellActionID, TileID, int, int],
        tuple[TemporalCocycle, OrderedBooleanSupport | None],
    ]
    support_symbol: Callable[
        [TileScheduler, FieldCellActionID, int, tuple[int, ...]],
        OrderedBooleanSupport | None,
    ]
    observe_symbol: Callable[
        [PrimitiveTileKernelAdapter, FieldCellActionID, int, object, tuple[int, ...]],
        TemporalCocycle | None,
    ]
    compile_leaf_output: Callable[
        [
            PrimitiveTileKernelAdapter,
            PrimitiveKernel,
            int,
            tuple[FinitePort, ...],
            FinitePort,
            FinitePort,
            AtomSort,
        ],
        FactoredFunctionID,
    ]
    compatibility_tile_admission_error: Callable[[BlockEffect], str | None] | None = (
        None
    )

    def __post_init__(self) -> None:
        if not isinstance(self.effect_type, type) or self.effect_type is BlockEffect:
            raise TypeError("family tile hook requires an exact effect type")
        if self.compatibility_type is not None and (
            not isinstance(self.compatibility_type, type)
            or self.compatibility_type is BlockEffect
            or self.compatibility_type is self.effect_type
        ):
            raise TypeError("family compatibility hook requires a distinct exact type")
        if (self.compatibility_type is None) != (
            self.lower_compatibility_effect is None
        ):
            raise TypeError("compatibility type and lowering callback must be paired")
        compatibility_callbacks = (
            self.validate_compatibility_effect,
            self.compatibility_right_halo,
            self.compatibility_right_reset_radius,
            self.compatibility_tile_admission_error,
        )
        if self.compatibility_type is None:
            if any(callback is not None for callback in compatibility_callbacks):
                raise TypeError("compatibility callbacks require a compatibility type")
        elif any(not callable(callback) for callback in compatibility_callbacks):
            raise TypeError(
                "compatibility hooks require validation and geometry callbacks"
            )
        profile_callbacks = (
            self.validate_source_profile_action,
            self.make_source_profile,
        )
        if self.source_profile_type is None:
            if any(callback is not None for callback in profile_callbacks):
                raise TypeError(
                    "source profile callbacks require an exact profile type"
                )
        elif not isinstance(self.source_profile_type, type) or any(
            not callable(callback) for callback in profile_callbacks
        ):
            raise TypeError("source profile hook requires exact typed callbacks")
        if self.lower_compatibility_effect is not None and not callable(
            self.lower_compatibility_effect
        ):
            raise TypeError("compatibility lowering must be callable")
        if self.certified_program_leaf is not None and not callable(
            self.certified_program_leaf
        ):
            raise TypeError("family certificate leaf verifier must be callable")
        cycle_callbacks = (
            self.make_cycle_projection,
            self.validate_cycle_projection,
            self.project_cycle_point,
            self.project_cycle_width,
        )
        if self.cycle_projection_type is None:
            if any(callback is not None for callback in cycle_callbacks):
                raise TypeError("cycle projection type and callbacks must be paired")
        elif not isinstance(self.cycle_projection_type, type) or any(
            not callable(callback) for callback in cycle_callbacks
        ):
            raise TypeError("cycle projection requires an exact type and callbacks")
        if type(self.spatial_events_add) is not bool:
            raise TypeError("family spatial-event flag must be Boolean")
        if any(
            not callable(callback)
            for callback in (
                self.clone_effect,
                self.make_support_arena,
                self.primitive_support,
                self.complete_clock,
                self.initial_event_shift,
                self.observe_primitive,
                self.observe_source_tile,
                self.support_symbol,
                self.observe_symbol,
                self.compile_leaf_output,
            )
        ):
            raise TypeError("family tile hooks require callable implementations")

    def owns_effect(self, effect: BlockEffect) -> bool:
        return type(effect) is self.effect_type

    def owns_compatibility(self, effect: BlockEffect) -> bool:
        return (
            self.compatibility_type is not None
            and type(effect) is self.compatibility_type
        )

    def validate_compatibility(self, effect: BlockEffect) -> None:
        if not self.owns_compatibility(effect):
            raise TypeError("family hook received a foreign compatibility effect")
        validate = self.validate_compatibility_effect
        if validate is None:
            raise TypeError("family hook has no compatibility validator")
        validate(effect)

    def compatibility_tile_error(self, effect: BlockEffect) -> str | None:
        """Validate a compatibility effect and report its tile-specific rejection."""
        self.validate_compatibility(effect)
        callback = self.compatibility_tile_admission_error
        if callback is None:
            return None
        message = callback(effect)
        if message is not None and (type(message) is not str or not message):
            raise TypeError("compatibility tile error must be a nonempty string")
        return message

    def compatibility_halo(self, effect: BlockEffect) -> int | None:
        return self._compatibility_geometry(
            effect, self.compatibility_right_halo, "right halo"
        )

    def compatibility_reset_radius(self, effect: BlockEffect) -> int | None:
        return self._compatibility_geometry(
            effect,
            self.compatibility_right_reset_radius,
            "right reset radius",
        )

    def admits_source_profile(
        self, runtime: DiamondRuntime, action: ActionProgramID
    ) -> bool:
        check = self.validate_source_profile_action
        if check is None:
            return False
        result = check(runtime, action)
        if type(result) is not bool:
            raise TypeError("source profile validator must return an exact Boolean")
        return result

    def source_profile(
        self, runtime: DiamondRuntime, action: ActionProgramID
    ) -> object:
        if not self.admits_source_profile(runtime, action):
            raise ValueError("family hook rejected this source profile action")
        make = self.make_source_profile
        if make is None:
            raise TypeError("family hook has no source profile loader")
        result = make(runtime, action)
        if type(result) is not self.source_profile_type:
            raise TypeError("family source profile loader returned another type")
        return result

    def _compatibility_geometry(
        self,
        effect: BlockEffect,
        callback: Callable[[BlockEffect], int | None] | None,
        label: str,
    ) -> int | None:
        self.validate_compatibility(effect)
        if callback is None:
            raise TypeError(f"family hook has no compatibility {label} projection")
        result = callback(effect)
        if result is not None and (type(result) is not int or result < 0):
            raise TypeError(f"compatibility {label} must be a nonnegative integer")
        return result

    def lower_compatibility(
        self, effect: BlockEffect, compiler: LazyCompiler
    ) -> BlockEffect:
        if not self.owns_compatibility(effect):
            raise TypeError("family hook received a foreign compatibility effect")
        lower = self.lower_compatibility_effect
        if lower is None:
            raise TypeError("family hook does not lower compatibility effects")
        lowered = lower(effect, compiler)
        if lowered.base != effect.base or lowered.blank != effect.blank:
            raise ValueError("compatibility lowering changed the cell alphabet")
        if lowered.exponent != effect.exponent:
            raise ValueError("compatibility lowering changed the temporal span")
        return lowered

    def program_leaf_counts(self, effect: BlockEffect) -> tuple[int, int] | None:
        verifier = self.certified_program_leaf
        if verifier is None:
            return None
        result = verifier(effect)
        if result is None:
            return None
        if (
            type(result) is not tuple
            or len(result) != 2
            or any(type(value) is not int or value < 0 for value in result)
        ):
            raise TypeError("family certificate callback returned invalid counts")
        return result

    def make_cycle(
        self, runtime: DiamondRuntime, root: ActionProgramID
    ) -> object | None:
        make = self.make_cycle_projection
        if make is None:
            return None
        projection = make(runtime, root)
        if projection is None:
            return None
        if type(projection) is not self.cycle_projection_type:
            raise TypeError("family cycle builder returned another projection type")
        if not self.validate_cycle(runtime, root, projection):
            raise ValueError(
                "family cycle builder returned an unauthenticated projection"
            )
        return projection

    def is_cycle_projection(self, value: object) -> bool:
        return (
            self.cycle_projection_type is not None
            and type(value) is self.cycle_projection_type
        )

    def validate_cycle(
        self, runtime: DiamondRuntime, root: ActionProgramID, projection: object
    ) -> bool:
        validate = self.validate_cycle_projection
        if validate is None or not self.is_cycle_projection(projection):
            return False
        result = validate(runtime, root, projection)
        if type(result) is not bool:
            raise TypeError("family cycle validator must return an exact Boolean")
        return result

    def cycle_point(self, projection: object, coordinate: int) -> int:
        if not self.is_cycle_projection(projection):
            raise TypeError("cycle point requires a canonical family projection")
        result = self._require_cycle_callback(self.project_cycle_point)(
            projection, coordinate
        )
        if type(result) is not int:
            raise TypeError("family cycle point must return an exact symbol")
        return result

    def cycle_width(self, projection: object, maximum: int | None) -> int:
        if not self.is_cycle_projection(projection):
            raise TypeError("cycle width requires a canonical family projection")
        result = self._require_cycle_callback(self.project_cycle_width)(
            projection, maximum
        )
        if type(result) is not int:
            raise TypeError("family cycle width must return an exact integer")
        return result

    @staticmethod
    def _require_cycle_callback(
        callback: Callable[..., object] | None,
    ) -> Callable[..., object]:
        if callback is None:
            raise TypeError("family has no cycle projection callback")
        return callback

    def clone(self, effect: BlockEffect) -> BlockEffect:
        if not self.owns_effect(effect):
            raise TypeError("family hook received a foreign primitive effect")
        clone = self.clone_effect(effect)
        if type(clone) is not self.effect_type:
            raise TypeError("family hook returned a noncanonical primitive effect")
        if _effect_key(clone) != _effect_key(effect):
            raise ValueError("family effect clone changed semantic authority")
        return clone

    def support_arena(
        self, max_nodes: int, ledger: ResourceLedger
    ) -> OrderedBooleanSupportArena:
        arena = self.make_support_arena(max_nodes, ledger)
        if (
            not isinstance(arena, OrderedBooleanSupportArena)
            or arena.ledger is not ledger
        ):
            raise ValueError("family support arena has another resource owner")
        return arena

    def physical_support(
        self,
        scheduler: TileScheduler,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
    ) -> OrderedBooleanSupport | None:
        support = self.primitive_support(scheduler, action, source, ports)
        if support is not None:
            if not isinstance(support, OrderedBooleanSupport):
                raise TypeError("family hook returned an invalid support node")
            support.owner.validate(support)
        return support

    def source_tile_observation(
        self,
        scheduler: TileScheduler,
        action: FieldCellActionID,
        source: TileID,
        left: int,
        right: int,
    ) -> tuple[TemporalCocycle, OrderedBooleanSupport | None]:
        observation, support = self.observe_source_tile(
            scheduler, action, source, left, right
        )
        if type(observation) is not TemporalCocycle:
            raise TypeError("family source observer returned another cocycle")
        if support is not None:
            if not isinstance(support, OrderedBooleanSupport):
                raise TypeError("family source observer returned an invalid support")
            support.owner.validate(support)
        return observation, support

    def symbol_support(
        self,
        scheduler: TileScheduler,
        action: FieldCellActionID,
        symbol: int,
        ports: tuple[int, ...],
    ) -> OrderedBooleanSupport | None:
        support = self.support_symbol(scheduler, action, symbol, ports)
        if support is not None:
            if not isinstance(support, OrderedBooleanSupport):
                raise TypeError("family symbol observer returned an invalid support")
            support.owner.validate(support)
        return support

    def finish_clock(
        self,
        scheduler: TileScheduler,
        key: PoweredResultKey,
        *,
        whole_output: bool,
    ) -> ResultLease | None:
        from number_compiler.hashlife.tiles.tile_results import ResultLease

        result = self.complete_clock(scheduler, key, whole_output)
        if result is None:
            return None
        if type(result) is not ResultLease:
            raise TypeError("family clock completion returned another lease type")
        if result._issuer is not scheduler.results or result._key != key:
            raise ValueError("family clock completion returned a foreign result")
        _ = result.result
        return result

    def shifted_event(
        self, scheduler: TileScheduler, key: PoweredResultKey
    ) -> tuple[FieldCellActionID, int] | None:
        return self.initial_event_shift(scheduler, key)


class TileExecutionAdapter(Protocol):
    """Fixed-interface family law consumed by the shared scheduler."""

    complete_via_midpoint_tiles: bool
    family_hooks: FamilyTileHooks | None

    def validate_action(self, action: FieldCellActionID) -> None: ...

    def validate_wiring(
        self,
        action: FieldCellActionID,
        wiring: ResultWiring,
    ) -> None: ...

    def action_children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...

    def action_cocycle(self, action: FieldCellActionID) -> TemporalCocycle: ...

    def leaf_observation(
        self,
        action: FieldCellActionID,
        source: TileID,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> TemporalCocycle: ...

    def leaf_interface(
        self,
        action: FieldCellActionID,
        source: TileID,
        wiring: ResultWiring,
    ) -> LocalInterfaceID: ...

    def apply_leaf(
        self,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> PrimitiveTileResult: ...

    def child_context(
        self,
        action: FieldCellActionID,
        parent: TileID,
        left: TileID,
        right: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
    ) -> ChildContext: ...

    def join_semantics(
        self,
        action: FieldCellActionID,
        parent: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        left: CompletedResult,
        right: CompletedResult,
    ) -> ResultSemantics: ...

    def temporal_before_context(
        self,
        action: FieldCellActionID,
        before: FieldCellActionID,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ChildContext: ...

    def temporal_after_context(
        self,
        action: FieldCellActionID,
        after: FieldCellActionID,
        before_result: CompletedResult,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ChildContext: ...

    def temporal_semantics(
        self,
        action: FieldCellActionID,
        before: CompletedResult,
        after: CompletedResult,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ResultSemantics: ...

    def output_active(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> bool: ...


__all__ = ["FamilyTileHooks", "TileExecutionAdapter"]
