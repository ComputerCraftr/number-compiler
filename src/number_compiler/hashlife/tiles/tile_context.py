"""Bounded execution contexts shared by tile scheduler and family adapters."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.tiles.ordered_boolean_support import OrderedBooleanSupport
from number_compiler.hashlife.tiles.temporal_cocycle import (
    TemporalCocycle as _TemporalCocycle,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    EMPTY_BOUNDARY_TILES,
    BoundaryTileOperands,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import CompletedResult
from number_compiler.hashlife.tiles.tiles import TileID

TemporalCocycle = _TemporalCocycle

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey


def _validate_boundary_shape(value: BoundaryTileOperands) -> None:
    if type(value) is not BoundaryTileOperands:
        raise TypeError("execution context requires a fixed boundary tile pair")
    value.__post_init__()


@dataclass(frozen=True, slots=True)
class ResultSemantics:
    """The bounded part of a result, excluding its exact output tile."""

    outgoing: LocalInterfaceID
    outgoing_ports: tuple[int, ...]
    physical_ticks: int = 0
    event_weight: int = 0
    frame_shift: int = 0
    relative_origin: int = 0
    relative_extent: int = 0
    outgoing_boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES
    fusion: FusedBoundaryContract | None = None
    observed_input_ports: tuple[int, ...] | None = None
    physical_support: OrderedBooleanSupport | None = None

    def __post_init__(self) -> None:
        _validate_boundary_shape(self.outgoing_boundaries)
        if type(self.outgoing) is not LocalInterfaceID:
            raise TypeError("result semantics require a local interface ID")
        if type(self.outgoing_ports) is not tuple or any(
            type(value) is not int for value in self.outgoing_ports
        ):
            raise TypeError("result semantics require exact immutable ports")
        values = (
            self.physical_ticks,
            self.event_weight,
            self.frame_shift,
            self.relative_origin,
            self.relative_extent,
        )
        if any(type(value) is not int for value in values):
            raise TypeError("result semantics require exact integer metadata")
        if self.physical_ticks < 0 or self.event_weight < 0:
            raise ValueError("result weights cannot be negative")
        if self.relative_extent < 0:
            raise ValueError("relative extent cannot be negative")
        if self.fusion is not None and type(self.fusion) is not FusedBoundaryContract:
            raise TypeError("result semantics fusion has another sort")
        if self.fusion is not None:
            self.fusion.__post_init__()
        if self.observed_input_ports is not None and (
            type(self.observed_input_ports) is not tuple
            or any(type(value) is not int for value in self.observed_input_ports)
        ):
            raise TypeError("observed input ports require exact immutable integers")
        if self.physical_support is not None:
            if not isinstance(self.physical_support, OrderedBooleanSupport):
                raise TypeError("result semantics has another shadow-support sort")
            self.physical_support.owner.validate(self.physical_support)

    def completed(self, output: TileID) -> CompletedResult:
        return CompletedResult(
            output,
            self.outgoing,
            self.outgoing_ports,
            self.physical_ticks,
            self.event_weight,
            self.frame_shift,
            self.relative_origin,
            self.relative_extent,
            self.outgoing_boundaries,
            self.fusion,
            self.observed_input_ports,
            self.physical_support,
        )


@dataclass(frozen=True, slots=True)
class PrimitiveTileResult:
    symbol: int
    semantics: ResultSemantics

    def __post_init__(self) -> None:
        if type(self.symbol) is not int:
            raise TypeError("primitive output requires an exact symbol")
        if type(self.semantics) is not ResultSemantics:
            raise TypeError("primitive output requires complete semantics")
        if any(
            (
                self.semantics.physical_ticks,
                self.semantics.event_weight,
                self.semantics.frame_shift,
            )
        ):
            raise ValueError("leaf interfaces cannot own temporal cocycles")


@dataclass(frozen=True, slots=True)
class ChildContext:
    ports: tuple[int, ...]
    wiring: ResultWiring
    boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES

    def __post_init__(self) -> None:
        if type(self.ports) is not tuple or any(
            type(value) is not int for value in self.ports
        ):
            raise TypeError("child context requires exact immutable ports")
        if type(self.wiring) is not ResultWiring:
            raise TypeError("child context requires normalized wiring")
        self.wiring.__post_init__()
        _validate_boundary_shape(self.boundaries)


def before_context(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    before: FieldCellActionID,
) -> ChildContext:
    """Select the producer contract at this temporal edge, without resetting it."""
    if key.fusion is not None:
        bound = key.fusion.producer
        return ChildContext(bound.ports, bound.wiring, bound.boundaries)
    return scheduler.adapter.temporal_before_context(
        key.action,
        before,
        key.ports,
        key.wiring,
    )


def bind_context(
    scheduler: TileScheduler,
    action: FieldCellActionID,
    context: BoundPorts,
) -> BoundPorts:
    """Resolve exact exterior operands only on an uncached execution path."""
    from collections.abc import Callable
    from typing import cast

    if context.boundaries == BoundaryTileOperands():
        return context
    hook = getattr(scheduler.adapter, "bind_boundaries", None)
    if hook is None:
        from number_compiler.hashlife.actions.lazy_compiler import (
            UnsupportedInterfaceError,
        )

        raise UnsupportedInterfaceError(
            "adapter cannot consume exact boundary operands"
        )
    bound = cast("Callable[[FieldCellActionID, BoundPorts], BoundPorts]", hook)(
        action, context
    )
    if type(bound) is not BoundPorts:
        raise TypeError("boundary binding returned another port contract")
    scheduler.results.validate_shape(action, bound.ports, bound.wiring)
    if bound.boundaries != BoundaryTileOperands():
        raise ValueError("primitive boundary binding retained an unconsumed operand")
    return bound


def after_context(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    after: FieldCellActionID,
    midpoint: CompletedResult,
) -> ChildContext:
    """Consume a midpoint under the consumer's own incoming contract."""
    if key.fusion is not None:
        bound = key.fusion.consumer
        return ChildContext(bound.ports, bound.wiring, bound.boundaries)
    return scheduler.adapter.temporal_after_context(
        key.action,
        after,
        midpoint,
        key.ports,
        key.wiring,
    )


def temporal_result(
    scheduler: TileScheduler,
    key: PoweredResultKey,
    before: CompletedResult,
    after: CompletedResult,
) -> CompletedResult:
    """Compose cocycles and retain both outgoing contracts of this edge."""
    from dataclasses import replace

    semantics = scheduler.adapter.temporal_semantics(
        key.action,
        before,
        after,
        key.ports,
        key.wiring,
    )
    if type(semantics) is not ResultSemantics:
        raise TypeError("temporal composition returned incomplete semantics")
    if key.fusion is not None:
        semantics = replace(
            semantics,
            outgoing_boundaries=after.outgoing_boundaries,
            fusion=FusedBoundaryContract(
                BoundPorts(
                    before.outgoing_ports,
                    key.fusion.producer.wiring,
                    before.outgoing_boundaries,
                ),
                BoundPorts(after.outgoing_ports, key.wiring, after.outgoing_boundaries),
            ),
        )
    return semantics.completed(after.output)


def validate_midpoint_exits(
    left_context: ChildContext,
    right_context: ChildContext,
    left: CompletedResult,
    right: CompletedResult,
) -> None:
    """Check the two independently executed directed crossings before joining."""
    if any(
        len(value) != 2
        for value in (
            left_context.ports,
            right_context.ports,
            left.outgoing_ports,
            right.outgoing_ports,
        )
    ):
        raise ValueError("two-sided midpoint checks require two finite channels")
    if left.outgoing_ports[0] != right_context.ports[0]:
        raise ValueError("left output disagrees with the forward midpoint transfer")
    if right.outgoing_ports[1] != left_context.ports[1]:
        raise ValueError("right output disagrees with the backward midpoint transfer")
