"""Frozen identities and values used by canonical tile result stores."""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.future_behavior import (
    FutureBehaviorClassID,
    FutureBehaviorProfileID,
)
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.tiles.tile_boundaries import (
    EMPTY_BOUNDARY_TILES,
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tiles import TileAlphabetID, TileID
from number_compiler.sequences.collatz.physical_support import PhysicalSupport


@dataclass(frozen=True, slots=True)
class PoweredResultKey:
    action: FieldCellActionID
    input: TileID
    ports: tuple[int, ...]
    wiring: ResultWiring
    boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES
    fusion: FusedBoundaryContract | None = None
    region: tuple[int, int] | None = None

    @property
    def bound_ports(self) -> BoundPorts:
        return BoundPorts(self.ports, self.wiring, self.boundaries)


@dataclass(frozen=True, slots=True)
class PoweredInterfaceKey:
    action: FieldCellActionID
    input: TileID
    wiring: ResultWiring
    boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES


@dataclass(frozen=True, slots=True)
class DirectedTransferKey:
    """One primitive directed transfer over an exact canonical input tile."""

    action: FieldCellActionID
    input: TileID
    side: int
    incoming_state: int
    wiring: ResultWiring

    @property
    def boundaries(self) -> BoundaryTileOperands:
        return EMPTY_BOUNDARY_TILES


@dataclass(frozen=True, slots=True)
class ReverseThresholdSummaryKey:
    """One canonical LT/EQ/GT reset summary for an exact pair tile.

    The radix is explicit because equal numeric leaf symbols in alphabets with
    different threshold interpretations must not share arithmetic summaries.
    """

    input: TileID
    base: int

    def __post_init__(self) -> None:
        if type(self.input) is not TileID:
            raise TypeError("reverse threshold summary requires a scoped tile ID")
        if type(self.base) is not int:
            raise TypeError("reverse threshold summary requires an exact radix")
        if self.base < 2:
            raise ValueError("reverse threshold summary radix must be at least two")


@dataclass(frozen=True, slots=True)
class ReverseBoundOutputKey:
    """One exact tile's context-independent bounded reverse output law."""

    input: TileID

    def __post_init__(self) -> None:
        if type(self.input) is not TileID:
            raise TypeError("reverse bound output requires a scoped tile ID")


@dataclass(frozen=True, slots=True)
class SourceRootMatchKey:
    """One binary source tile compared with both phases of ``-1/3``."""

    input: TileID

    def __post_init__(self) -> None:
        if type(self.input) is not TileID:
            raise TypeError("source root match requires a scoped tile ID")


@dataclass(frozen=True, slots=True)
class RootMatchResult:
    """First mismatch geometry for the two alternating root phases."""

    level: int
    phase0_first_mismatch: int | None
    phase1_first_mismatch: int | None
    _publication_owner: object | None = None
    _publication_snapshot: tuple[object, ...] | None = None

    def __post_init__(self) -> None:
        if type(self.level) is not int or self.level < 0:
            raise ValueError("source root match requires a nonnegative level")
        width = 1 << self.level
        for mismatch in (
            self.phase0_first_mismatch,
            self.phase1_first_mismatch,
        ):
            if mismatch is not None and (
                type(mismatch) is not int or not 0 <= mismatch < width
            ):
                raise ValueError("source root mismatch lies outside its tile")
        if (
            self._publication_snapshot is not None
            and type(self._publication_snapshot) is not tuple
        ):
            raise TypeError("source root publication snapshot must be immutable")


@dataclass(frozen=True, slots=True)
class NormalizedRegionKey:
    """One exact clipped tile view before spatial canonicalization."""

    view: BoundaryTileView

    @property
    def input(self) -> TileID:
        return self.view.tile


@dataclass(frozen=True, slots=True)
class NormalizedRegionResult:
    """Sealed canonical exact content for one clipped tile occurrence."""

    view: BoundaryTileView
    _publication_owner: object | None = None
    _publication_snapshot: tuple[object, ...] | None = None

    def __post_init__(self) -> None:
        if type(self.view) is not BoundaryTileView:
            raise TypeError("normalized region result requires an exact boundary view")
        self.view.__post_init__()
        if (
            self._publication_snapshot is not None
            and type(self._publication_snapshot) is not tuple
        ):
            raise TypeError("normalized region publication snapshot must be immutable")


@dataclass(frozen=True, slots=True)
class BoundaryConcatKey:
    """Two exact canonical boundary operands before spatial concatenation."""

    alphabet: TileAlphabetID
    first: BoundaryTileView
    second: BoundaryTileView


@dataclass(frozen=True, slots=True)
class BoundaryConcatResult:
    """Sealed canonical content produced by concatenating two exact views."""

    view: BoundaryTileView
    _publication_owner: object | None = None
    _publication_snapshot: tuple[object, ...] | None = None

    def __post_init__(self) -> None:
        if type(self.view) is not BoundaryTileView:
            raise TypeError("boundary concat result requires an exact boundary view")
        self.view.__post_init__()
        if (
            self._publication_snapshot is not None
            and type(self._publication_snapshot) is not tuple
        ):
            raise TypeError("boundary concat publication snapshot must be immutable")


@dataclass(frozen=True, slots=True)
class CausalInterfaceKey:
    """One complete output-independent causal parent observation."""

    action: FieldCellActionID
    input: TileID
    ports: tuple[int, ...]
    wiring: ResultWiring
    boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES
    fusion: FusedBoundaryContract | None = None
    observation: str = field(default="interface", kw_only=True)


@dataclass(frozen=True, slots=True)
class CompletedInterfaceResult:
    """Bounded causal behavior with no exact final-output tile."""

    interface: LocalInterfaceID
    observed_input_ports: tuple[int, ...]
    outgoing_ports: tuple[int, ...]
    level: int
    active: bool
    physical_ticks: int = 0
    event_weight: int = 0
    frame_shift: int = 0
    physical_support: PhysicalSupport | None = field(default=None, kw_only=True)
    bound_reverse_output: ReverseBoundOutput | None = field(default=None, kw_only=True)
    _publication_owner: object | None = None
    _publication_snapshot: tuple[object, ...] | None = None

    def __post_init__(self) -> None:
        if type(self.interface) is not LocalInterfaceID:
            raise TypeError("completed interface requires a local interface ID")
        for values in (self.observed_input_ports, self.outgoing_ports):
            if type(values) is not tuple or any(
                type(value) is not int for value in values
            ):
                raise TypeError("completed interface ports require exact integers")
        if type(self.level) is not int or self.level < 0:
            raise ValueError("completed interface requires a nonnegative exact level")
        if type(self.active) is not bool:
            raise TypeError("completed interface activity requires an exact Boolean")
        if any(
            type(value) is not int
            for value in (
                self.physical_ticks,
                self.event_weight,
                self.frame_shift,
            )
        ):
            raise TypeError("completed interface weights require exact integers")
        if self.physical_ticks < 0 or self.event_weight < 0:
            raise ValueError("completed interface weights cannot be negative")
        if self.physical_support is not None:
            if type(self.physical_support) is not PhysicalSupport:
                raise TypeError("completed interface has another shadow-support sort")
            self.physical_support.owner.validate(self.physical_support)
            if self.physical_support.ticks and (
                self.physical_support.ticks != self.physical_ticks
                or self.physical_support.odd_ticks != self.event_weight
            ):
                raise ValueError("completed interface support disagrees with weights")
        if self.bound_reverse_output is not None:
            if type(self.bound_reverse_output) is not ReverseBoundOutput:
                raise TypeError("completed interface has another active behavior sort")
            self.bound_reverse_output.__post_init__()
        if (
            self._publication_snapshot is not None
            and type(self._publication_snapshot) is not tuple
        ):
            raise TypeError(
                "completed interface publication snapshot must be immutable"
            )

    @property
    def retained_nodes(self) -> int:
        output = self.bound_reverse_output
        return 0 if output is None else output.retained_slots


@dataclass(frozen=True, slots=True)
class BehaviorBindingKey:
    """Occurrence binding from one exact request to a certified behavior class."""

    request: PoweredResultKey
    profile: FutureBehaviorProfileID

    @property
    def action(self) -> FieldCellActionID:
        return self.request.action

    @property
    def input(self) -> TileID:
        return self.request.input

    @property
    def boundaries(self) -> BoundaryTileOperands:
        return self.request.boundaries

    @property
    def ports(self) -> tuple[int, ...]:
        return self.request.ports

    @property
    def wiring(self) -> ResultWiring:
        return self.request.wiring

    @property
    def fusion(self) -> FusedBoundaryContract | None:
        return self.request.fusion

    @property
    def region(self) -> tuple[int, int] | None:
        return self.request.region


@dataclass(frozen=True, slots=True)
class CompletedBehaviorClassification:
    behavior: FutureBehaviorClassID
    _publication_owner: object | None = None
    _publication_snapshot: tuple[object, ...] | None = None

    def __post_init__(self) -> None:
        if type(self.behavior) is not FutureBehaviorClassID:
            raise TypeError("completed behavior requires a scoped behavior class")
        if (
            self._publication_snapshot is not None
            and type(self._publication_snapshot) is not tuple
        ):
            raise TypeError("behavior publication snapshot must be immutable")


@dataclass(frozen=True, slots=True)
class FusedInterfaceKey:
    """A consumer interface parameterized by one concrete producer context."""

    action: FieldCellActionID
    input: TileID
    ports: tuple[int, ...]
    wiring: ResultWiring
    producer_wiring: ResultWiring | None = None
    boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES
    before: FieldCellActionID | None = None
    after: FieldCellActionID | None = None
    consumer_boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES

    def __post_init__(self) -> None:
        if self.producer_wiring is None:
            object.__setattr__(self, "producer_wiring", self.wiring)
        elif type(self.producer_wiring) is not ResultWiring:
            raise TypeError("fused producer requires normalized wiring")
        if type(self.boundaries) is not BoundaryTileOperands:
            raise TypeError("fused interfaces require exact boundary operands")
        self.boundaries.__post_init__()
        if (self.before is None) != (self.after is None):
            raise ValueError("fused edge requires both temporal children")
        if self.before is not None and (
            type(self.before) is not FieldCellActionID
            or type(self.after) is not FieldCellActionID
        ):
            raise TypeError("fused edge requires scoped temporal children")
        if type(self.consumer_boundaries) is not BoundaryTileOperands:
            raise TypeError("fused consumer requires exact boundary operands")
        self.consumer_boundaries.__post_init__()

    @property
    def producer_context(self) -> BoundPorts:
        producer_wiring = self.producer_wiring
        if type(producer_wiring) is not ResultWiring:
            raise TypeError("fused producer requires normalized wiring")
        return BoundPorts(self.ports, producer_wiring, self.boundaries)


@dataclass(frozen=True, slots=True)
class SpatialInterfaceKey:
    left: LocalInterfaceID
    right: LocalInterfaceID
    wiring: ResultWiring


@dataclass(frozen=True, slots=True)
class CompletedResult:
    output: TileID
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
    physical_support: PhysicalSupport | None = None

    def __post_init__(self) -> None:
        if type(self.output) is not TileID:
            raise TypeError("completed output requires a scoped tile ID")
        if type(self.outgoing) is not LocalInterfaceID:
            raise TypeError("completed output requires a scoped local interface")
        if type(self.outgoing_ports) is not tuple or any(
            type(value) is not int for value in self.outgoing_ports
        ):
            raise TypeError("completed result ports require exact immutable integers")
        metadata = (
            self.physical_ticks,
            self.event_weight,
            self.frame_shift,
            self.relative_origin,
            self.relative_extent,
        )
        if any(type(value) is not int for value in metadata):
            raise TypeError("completed result metadata requires exact integers")
        if self.physical_ticks < 0 or self.event_weight < 0 or self.relative_extent < 0:
            raise ValueError("completed result weights and extent cannot be negative")
        if type(self.outgoing_boundaries) is not BoundaryTileOperands:
            raise TypeError("completed result requires exact outgoing boundaries")
        self.outgoing_boundaries.__post_init__()
        if self.fusion is not None and type(self.fusion) is not FusedBoundaryContract:
            raise TypeError("completed result contract has another sort")
        if self.fusion is not None:
            self.fusion.__post_init__()
        if self.observed_input_ports is not None and (
            type(self.observed_input_ports) is not tuple
            or any(type(value) is not int for value in self.observed_input_ports)
        ):
            raise TypeError("observed input ports require exact immutable integers")
        if self.physical_support is not None:
            if type(self.physical_support) is not PhysicalSupport:
                raise TypeError("completed result has another shadow-support sort")
            self.physical_support.owner.validate(self.physical_support)


@dataclass(frozen=True, slots=True)
class _FusedVariantKey:
    action: FieldCellActionID
    input: TileID
    wiring: ResultWiring
    producer_wiring: ResultWiring
    boundaries: BoundaryTileOperands
    before: FieldCellActionID | None
    after: FieldCellActionID | None
    consumer_boundaries: BoundaryTileOperands


@dataclass(frozen=True, slots=True)
class _ResultVariantKey:
    action: FieldCellActionID
    input: TileID
    wiring: ResultWiring
    boundaries: BoundaryTileOperands
    producer: BoundPorts | None
    region: tuple[int, int] | None = None


@dataclass(frozen=True, slots=True)
class _ReverseHead:
    tile: TileID


@dataclass(frozen=True, slots=True)
class _ReverseMember:
    tile: TileID
    key: (
        PoweredResultKey
        | PoweredInterfaceKey
        | FusedInterfaceKey
        | CausalInterfaceKey
        | DirectedTransferKey
        | ReverseThresholdSummaryKey
        | ReverseBoundOutputKey
        | SourceRootMatchKey
        | BehaviorBindingKey
        | NormalizedRegionKey
        | BoundaryConcatKey
    )


@dataclass(frozen=True, slots=True)
class _ReverseLinks:
    previous: (
        PoweredResultKey
        | PoweredInterfaceKey
        | FusedInterfaceKey
        | CausalInterfaceKey
        | DirectedTransferKey
        | ReverseThresholdSummaryKey
        | ReverseBoundOutputKey
        | SourceRootMatchKey
        | BehaviorBindingKey
        | NormalizedRegionKey
        | BoundaryConcatKey
        | None
    )
    following: (
        PoweredResultKey
        | PoweredInterfaceKey
        | FusedInterfaceKey
        | CausalInterfaceKey
        | DirectedTransferKey
        | ReverseThresholdSummaryKey
        | ReverseBoundOutputKey
        | SourceRootMatchKey
        | BehaviorBindingKey
        | NormalizedRegionKey
        | BoundaryConcatKey
        | None
    )


def handle_snapshot(value: object) -> tuple[object, ...]:
    return (
        type(value),
        getattr(value, "owner", None),
        getattr(value, "kind", None),
        getattr(value, "local_id", None),
    )


def _wiring_snapshot(value: object) -> tuple[object, ...]:
    return (
        type(value),
        handle_snapshot(getattr(value, "signature", None)),
        getattr(value, "orientation", None),
        getattr(value, "phase", None),
    )


def boundary_view_snapshot(value: object) -> tuple[object, ...] | None:
    if value is None:
        return None
    return (
        type(value),
        handle_snapshot(getattr(value, "tile", None)),
        getattr(value, "source_offset", None),
        getattr(value, "relative_origin", None),
        getattr(value, "relative_extent", None),
        getattr(value, "orientation", None),
    )


def _boundaries_snapshot(value: object) -> tuple[object, ...]:
    return (
        type(value),
        boundary_view_snapshot(getattr(value, "left", None)),
        boundary_view_snapshot(getattr(value, "right", None)),
    )


def _context_snapshot(value: object) -> tuple[object, ...]:
    return (
        type(value),
        tuple(getattr(value, "ports", ())),
        _wiring_snapshot(getattr(value, "wiring", None)),
        _boundaries_snapshot(getattr(value, "boundaries", None)),
    )


def _fusion_snapshot(value: object) -> tuple[object, ...] | None:
    if value is None:
        return None
    return (
        type(value),
        _context_snapshot(getattr(value, "producer", None)),
        _context_snapshot(getattr(value, "consumer", None)),
    )


def execution_request_snapshot(key: object) -> tuple[object, ...]:
    """Detach all request scalars from caller-owned frozen record objects."""
    return (
        type(key),
        handle_snapshot(getattr(key, "action", None)),
        handle_snapshot(getattr(key, "input", None)),
        tuple(getattr(key, "ports", ())),
        _wiring_snapshot(getattr(key, "wiring", None)),
        _boundaries_snapshot(getattr(key, "boundaries", None)),
        _fusion_snapshot(getattr(key, "fusion", None)),
        getattr(key, "region", None),
        getattr(key, "observation", None),
    )


def _reverse_output_snapshot(value: object) -> tuple[object, ...] | None:
    if value is None:
        return None
    left, right = getattr(value, "left", None), getattr(value, "right", None)
    return (
        type(value),
        type(left),
        getattr(left, "base", None),
        getattr(left, "has_active", None),
        getattr(left, "has_blank", None),
        getattr(left, "sinks", None),
        getattr(left, "carry", None),
        getattr(left, "last_symbol", None),
        type(right),
        getattr(right, "base", None),
        getattr(right, "forward", None),
        getattr(right, "backward", None),
    )


def _physical_support_snapshot(value: object) -> tuple[object, ...] | None:
    if value is None:
        return None
    return (
        type(value),
        getattr(value, "owner", None),
        getattr(value, "node_id", None),
        getattr(value, "ticks", None),
        getattr(value, "odd_ticks", None),
        getattr(value, "parity", None),
        id(getattr(value, "left", None)),
        id(getattr(value, "right", None)),
    )


def causal_interface_snapshot(
    key: CausalInterfaceKey,
    value: CompletedInterfaceResult,
) -> tuple[object, ...]:
    """Copy every identity/semantic scalar; never trust a retained key object."""
    return (
        execution_request_snapshot(key),
        handle_snapshot(value.interface),
        tuple(value.observed_input_ports),
        tuple(value.outgoing_ports),
        value.level,
        value.active,
        value.physical_ticks,
        value.event_weight,
        value.frame_shift,
        _physical_support_snapshot(value.physical_support),
        _reverse_output_snapshot(value.bound_reverse_output),
    )


__all__ = [
    "handle_snapshot",
    "boundary_view_snapshot",
    "execution_request_snapshot",
    "causal_interface_snapshot",
    "BehaviorBindingKey",
    "BoundaryConcatKey",
    "BoundaryConcatResult",
    "CausalInterfaceKey",
    "CompletedBehaviorClassification",
    "CompletedInterfaceResult",
    "CompletedResult",
    "DirectedTransferKey",
    "FusedInterfaceKey",
    "NormalizedRegionKey",
    "NormalizedRegionResult",
    "PoweredInterfaceKey",
    "PoweredResultKey",
    "ReverseBoundOutputKey",
    "ReverseThresholdSummaryKey",
    "RootMatchResult",
    "SourceRootMatchKey",
    "SpatialInterfaceKey",
    "_FusedVariantKey",
    "_ResultVariantKey",
    "_ReverseHead",
    "_ReverseLinks",
    "_ReverseMember",
]
