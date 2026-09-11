"""Store-free completed result validation operations."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.formula.summary import BlockSummary
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    BehaviorBindingKey,
    BoundaryConcatKey,
    BoundaryConcatResult,
    CausalInterfaceKey,
    CompletedResult,
    DirectedTransferKey,
    FusedInterfaceKey,
    NormalizedRegionKey,
    NormalizedRegionResult,
    PoweredInterfaceKey,
    PoweredResultKey,
    ReverseBoundOutputKey,
    ReverseThresholdSummaryKey,
    RootMatchResult,
    SourceRootMatchKey,
)
from number_compiler.hashlife.tiles.tile_result_validation import (
    validate_fusion_contexts,
    validate_output_region,
)
from number_compiler.hashlife.tiles.tiles import TileID, TileLease

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_result_types import (
        ExecutionKey as _ExecutionKey,
        ExecutionValue as _ExecutionValue,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena


def admit_validated_signature(
    authority: object,
) -> Callable[[FieldCellActionID], object] | None:
    """Admit one bound combined validator without granting cache authority."""
    callback = getattr(authority, "validated_signature_for", None)
    if callback is None:
        return None
    if not callable(callback) or getattr(callback, "__self__", None) is not authority:
        raise ValueError("combined action/signature validation must bind its authority")
    return cast(Callable[[FieldCellActionID], object], callback)


def _validate_fusion(
    self: CompletedResultArena,
    action: FieldCellActionID,
    fusion: FusedBoundaryContract,
    consumer: BoundPorts,
    expected: TileID,
    *,
    counted: bool = True,
    output: bool = False,
) -> int:
    return validate_fusion_contexts(
        self,
        action,
        fusion,
        consumer,
        expected,
        counted=counted,
        output=output,
    )


def _validate_action_wiring(
    self: CompletedResultArena,
    action: FieldCellActionID,
    wiring: ResultWiring,
) -> None:
    if type(action) is not FieldCellActionID:
        raise TypeError("powered result requires a scoped field action")
    if type(wiring) is not ResultWiring:
        raise TypeError("powered result requires normalized wiring")
    wiring.__post_init__()
    if self._validated_signature_for is None:
        self._validate_action(action)
        expected = self._signature_for(action)
    else:
        admitted = self._validated_signature_for(action)
        if type(admitted) is not PortSignatureID:
            raise TypeError(
                "combined action validation returned another signature sort"
            )
        expected = admitted
    self.interfaces.interface(expected)
    self.interfaces.interface(wiring.signature)
    if wiring.signature != expected:
        raise ValueError("powered result signature does not match its action")
    interface = self.interfaces.interface(wiring.signature)
    if wiring.orientation not in interface.orientations:
        raise ValueError("powered result orientation lies outside its signature")
    if wiring.phase >= interface.phase_count:
        raise ValueError("powered result phase lies outside its signature")


def _validate_result(
    self: CompletedResultArena,
    key: PoweredResultKey,
    result: CompletedResult,
) -> None:
    if type(result) is not CompletedResult:
        raise TypeError("expected a frozen completed result")
    result.__post_init__()
    output = self.tiles.resolve(result.output)
    validate_output_region(key.region)
    if key.region is not None and output.level != key.region[1]:
        raise ValueError("causal result has another output level")
    self._validate_boundaries(result.outgoing_boundaries, result.output)
    if self._validate_output is not None:
        self._validate_output(key.action, result.output)
    if result.relative_extent > output.width:
        raise ValueError("completed relative extent exceeds its output tile")
    if result.relative_extent != output.extent:
        raise ValueError("completed relative extent disagrees with its output tile")
    outgoing = self.interfaces.resolve(result.outgoing)
    if outgoing.signature != key.wiring.signature:
        raise ValueError("completed result has another port signature")
    self._validate_ports(outgoing.signature, result.outgoing_ports)
    if result.observed_input_ports is not None:
        self._validate_ports(key.wiring.signature, result.observed_input_ports)
    expected_consumer = BoundPorts(
        result.outgoing_ports,
        key.wiring,
        result.outgoing_boundaries,
    )
    if key.fusion is None:
        if result.fusion is not None:
            raise ValueError("direct result cannot publish fused boundary semantics")
    else:
        if result.fusion is None:
            raise ValueError("fused result omitted its outgoing boundary contract")
        self._validate_fusion(
            key.action,
            result.fusion,
            expected_consumer,
            result.output,
            output=True,
        )


def _validate_leased(
    self: CompletedResultArena,
    key: PoweredResultKey,
    result: CompletedResult,
    tile: TileLease,
    boundary_tiles: tuple[TileLease, ...],
    operand_views: tuple[BoundaryTileView, ...],
) -> None:
    """Validate an issued lease without requiring its evictable input key."""
    if type(key) is not PoweredResultKey or type(tile) is not TileLease:
        raise ValueError("malformed completed-result lease association")
    if type(key.input) is not TileID:
        raise ValueError("malformed completed-result input identity")
    # The input may lawfully have retired after memo eviction.  Its scoped,
    # non-recycled allocation identity must still belong to this tile arena.
    key.input.validate(
        self.tiles.owner,
        "canonical-tile",
        size=self.tiles._next_tile,
    )
    self._validate_boundary_allocations(key.boundaries)
    self._validate_action_wiring(key.action, key.wiring)
    self._validate_ports(key.wiring.signature, key.ports, counted=False)
    if key.fusion is not None:
        if type(key.fusion) is not FusedBoundaryContract:
            raise ValueError("malformed leased fusion contract")
        key.fusion.__post_init__()
        if key.fusion.consumer != key.bound_ports:
            raise ValueError("leased fusion consumer disagrees with its request")
        self._validate_bound_port_allocations(key.fusion.producer, counted=False)
        self._validate_bound_port_allocations(key.fusion.consumer, counted=False)
        if self._validate_fused_action is None:
            raise ValueError("action authority does not admit fused interfaces")
        self._validate_fused_action(key.action)
        if self._validate_fused_wiring is None:
            if key.fusion.producer.wiring != key.fusion.consumer.wiring:
                raise ValueError(
                    "action authority does not admit heterogeneous fused wiring"
                )
        else:
            self._validate_fused_wiring(
                key.action,
                key.fusion.producer.wiring,
                key.fusion.consumer.wiring,
            )
    result.__post_init__()
    if tile.tile != result.output:
        raise ValueError("completed-result lease pins another output")
    output = self.tiles.resolve(result.output)
    validate_output_region(key.region)
    if key.region is not None and output.level != key.region[1]:
        raise ValueError("causal result has another output level")
    if self._validate_output is not None:
        self._validate_output(key.action, result.output)
    if result.relative_extent != output.extent:
        raise ValueError("completed-result lease has another extent")
    outgoing = self.interfaces.resolve(result.outgoing)
    if outgoing.signature != key.wiring.signature:
        raise ValueError("completed-result lease has another interface")
    self._validate_ports(outgoing.signature, result.outgoing_ports, counted=False)
    if result.observed_input_ports is not None:
        self._validate_ports(
            key.wiring.signature,
            result.observed_input_ports,
            counted=False,
        )
    self._validate_boundaries(result.outgoing_boundaries, result.output)
    expected_consumer = BoundPorts(
        result.outgoing_ports,
        key.wiring,
        result.outgoing_boundaries,
    )
    if key.fusion is None:
        if result.fusion is not None:
            raise ValueError("direct result lease has fused boundary semantics")
    else:
        if result.fusion is None:
            raise ValueError("fused result lease lost its boundary contract")
        self._validate_fusion(
            key.action,
            result.fusion,
            expected_consumer,
            result.output,
            counted=False,
            output=True,
        )
    if type(boundary_tiles) is not tuple or any(
        type(value) is not TileLease for value in boundary_tiles
    ):
        raise ValueError("malformed completed-result boundary leases")
    if (
        tuple(value.tile for value in boundary_tiles)
        != self._result_tile_ids(result)[1:]
    ):
        raise ValueError("completed-result lease pins other boundary tiles")
    if operand_views != self._result_operand_views(result):
        raise ValueError("completed-result lease retains other boundary operands")
    if any(
        type(self._leased_boundary_operands.records.get(view)) is not int
        or self._leased_boundary_operands.records.get(view, 0) < 1
        for view in operand_views
    ):
        raise ValueError("completed-result boundary operand is not inventoried")


def _tiles_for(
    self: CompletedResultArena,
    key: _ExecutionKey,
    result: _ExecutionValue,
) -> tuple[TileID, ...]:
    if type(key) is BoundaryConcatKey:
        if type(result) is not BoundaryConcatResult:
            raise TypeError("boundary concat memo has another value sort")
        return self._unique_tiles((key.first.tile, key.second.tile, result.view.tile))
    if type(key) is NormalizedRegionKey:
        if type(result) is not NormalizedRegionResult:
            raise TypeError("normalized region memo has another value sort")
        return self._unique_tiles((key.input, result.view.tile))
    if type(key) is ReverseThresholdSummaryKey:
        if type(result) is not BlockSummary:
            raise TypeError("reverse threshold memo has another value sort")
        return (key.input,)
    if type(key) is ReverseBoundOutputKey:
        if type(result) is not ReverseBoundOutput:
            raise TypeError("reverse output memo has another value sort")
        return (key.input,)
    if type(key) is SourceRootMatchKey:
        if type(result) is not RootMatchResult:
            raise TypeError("source root memo has another value sort")
        return (key.input,)
    request = cast(
        PoweredResultKey
        | PoweredInterfaceKey
        | FusedInterfaceKey
        | CausalInterfaceKey
        | DirectedTransferKey
        | BehaviorBindingKey,
        key,
    )
    fused_tiles: tuple[TileID, ...] = ()
    if type(request) is PoweredResultKey and request.fusion is not None:
        fused_tiles = (
            *request.fusion.producer.boundaries.tile_ids(),
            *request.fusion.consumer.boundaries.tile_ids(),
        )
    if type(request) is CausalInterfaceKey and request.fusion is not None:
        fused_tiles = (
            *request.fusion.producer.boundaries.tile_ids(),
            *request.fusion.consumer.boundaries.tile_ids(),
        )
    if type(request) is BehaviorBindingKey and request.fusion is not None:
        fused_tiles = (
            *request.fusion.producer.boundaries.tile_ids(),
            *request.fusion.consumer.boundaries.tile_ids(),
        )
    if type(request) is FusedInterfaceKey:
        fused_tiles = request.consumer_boundaries.tile_ids()
    if type(request) is DirectedTransferKey:
        return (request.input,)
    key_tiles = (request.input, *request.boundaries.tile_ids(), *fused_tiles)
    if type(request) in (
        PoweredInterfaceKey,
        FusedInterfaceKey,
        CausalInterfaceKey,
        BehaviorBindingKey,
    ):
        return self._unique_tiles(key_tiles)
    if type(result) is not CompletedResult:
        raise TypeError("completed result memo has another value sort")
    return self._unique_tiles((*key_tiles, *self._result_tile_ids(result)))
