"""Completed-result publication contracts for causal tile recurrence.

This module owns no memo or semantic arena.  It translates the two transient
causal boundary sorts into the existing :class:`PoweredResultKey` and requires
the recurrence to provide complete outgoing semantics before publication.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import TYPE_CHECKING, TypeAlias, cast

from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.tiles.tile_boundaries import (
    EMPTY_BOUNDARY_TILES,
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_context import ResultSemantics, TemporalCocycle
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import (
    CompletedResultArena,
    ResultLease,
)
from number_compiler.hashlife.tiles.tiles import TileArena, TileID


@dataclass(frozen=True, slots=True)
class PrimitiveCausalPorts:
    """The two finite incoming states of one primitive causal scan."""

    left: int
    right: int

    def __post_init__(self) -> None:
        if type(self.left) is not int or type(self.right) is not int:
            raise TypeError("primitive causal ports require exact integers")

    @property
    def ports(self) -> tuple[int, int]:
        return self.left, self.right


@dataclass(frozen=True, slots=True)
class CompositeCausalPrefixes:
    """Exact input-space prefixes plus the composite's finite exterior ports.

    ``operands.left`` and ``operands.right`` encode the spatial content held by
    the transient causal ``_Prefix`` states.  Their order is semantic: left is
    scanned forward and right backward.  Empty operands represent the initial
    composite prefix and remain distinct from primitive finite states by sort.
    """

    ports: tuple[int, ...]
    operands: BoundaryTileOperands = EMPTY_BOUNDARY_TILES

    def __post_init__(self) -> None:
        if type(self.ports) is not tuple or any(
            type(value) is not int for value in self.ports
        ):
            raise TypeError("composite causal ports require exact integers")
        if type(self.operands) is not BoundaryTileOperands:
            raise TypeError("composite causal prefixes require exact tile operands")
        self.operands.__post_init__()


CausalInputState: TypeAlias = PrimitiveCausalPorts | CompositeCausalPrefixes


@dataclass(frozen=True, slots=True)
class CausalCompletedOutput:
    """Exact causal output paired with its executable outgoing contract.

    For a composed action, ``semantics.outgoing`` is the source-bound local
    interface of the final primitive stage over its immediate causal input.  It
    is not claimed to quotient the whole temporal trajectory.  Exact spatial
    dependence needed to continue the scan is carried separately by
    ``semantics.outgoing_boundaries``.
    """

    output: TileID
    semantics: ResultSemantics
    incoming_ports: tuple[int, int] | None = None

    def __post_init__(self) -> None:
        if type(self.output) is not TileID:
            raise TypeError("causal completed output requires a scoped tile ID")
        if type(self.semantics) is not ResultSemantics:
            raise TypeError("causal completed output requires result semantics")
        self.semantics.__post_init__()
        if self.incoming_ports is not None and (
            type(self.incoming_ports) is not tuple
            or len(self.incoming_ports) != 2
            or any(type(value) is not int for value in self.incoming_ports)
        ):
            raise TypeError("causal task inputs require two exact finite states")
        observed = self.semantics.observed_input_ports
        if (
            observed is not None
            and self.incoming_ports is not None
            and observed != self.incoming_ports
        ):
            raise ValueError("causal task inputs disagree with completed semantics")


def cached_causal_output(
    result: ResultLease,
    tiles: TileArena | None = None,
) -> CausalCompletedOutput:
    """Recover a transient payload from an arena-validated completed result."""
    if type(result) is not ResultLease:
        raise TypeError("cached causal output requires a completed-result lease")
    value = result.result
    authority = cast("PrimitiveTileKernelAdapter", result._issuer.action_authority)
    children = authority.action_children(result._key.action)
    observed = value.observed_input_ports
    if children is None:
        ports = result._key.ports
    elif observed is not None:
        ports = observed
    else:
        raise ValueError("cached composite result omitted its observed input ports")
    if len(ports) != 2:
        raise ValueError("cached causal output requires two incoming ports")
    boundaries = value.outgoing_boundaries
    if tiles is not None:
        if type(tiles) is not TileArena:
            raise TypeError("cached causal output requires its canonical tile arena")
        if not boundaries.tile_ids():
            node = tiles.resolve(value.output)
            boundaries = BoundaryTileOperands(
                BoundaryTileView(value.output, 0, node.width, 0, 0),
                BoundaryTileView(value.output, 0, node.width, 1, 0),
            )
    semantics = ResultSemantics(
        value.outgoing,
        value.outgoing_ports,
        value.physical_ticks,
        value.event_weight,
        value.frame_shift,
        value.relative_origin,
        value.relative_extent,
        boundaries,
        value.fusion,
        physical_support=value.physical_support,
    )
    return CausalCompletedOutput(
        value.output,
        semantics,
        (ports[0], ports[1]),
    )


def _causal_result_key(
    results: CompletedResultArena,
    action: FieldCellActionID,
    input_tile: TileID,
    state: CausalInputState,
    wiring: ResultWiring,
    *,
    action_admission: object | None = None,
) -> PoweredResultKey:
    """Build a request envelope for immediate validation by its consumer."""
    if type(results) is not CompletedResultArena:
        raise TypeError("causal result keys require the shared result arena")
    if action_admission is None:
        children_hook = getattr(results.action_authority, "action_children", None)
        if not callable(children_hook):
            raise TypeError("causal result keys require a temporal action authority")
        children = children_hook(action)
    else:
        from number_compiler.resources.causal_workspace import (
            admitted_action_metadata,
        )

        _signature, _kernel, record = admitted_action_metadata(
            action_admission, results.action_authority, action
        )
        children = record.children
    if type(state) is PrimitiveCausalPorts:
        if children is not None:
            raise ValueError("composed causal actions require exact prefix operands")
        request_ports: tuple[int, ...] = state.ports
        boundaries = EMPTY_BOUNDARY_TILES
    elif type(state) is CompositeCausalPrefixes:
        if children is None:
            raise ValueError("primitive causal actions require finite port states")
        request_ports = state.ports
        boundaries = state.operands
    else:
        raise TypeError("causal input state has another sort")
    return PoweredResultKey(action, input_tile, request_ports, wiring, boundaries)


def causal_result_key(
    results: CompletedResultArena,
    action: FieldCellActionID,
    input_tile: TileID,
    state: CausalInputState,
    wiring: ResultWiring,
    *,
    action_admission: object | None = None,
) -> PoweredResultKey:
    """Build and validate a key which may escape before its next consumer."""
    key = _causal_result_key(
        results, action, input_tile, state, wiring, action_admission=action_admission
    )
    # Validate owner/kind/allocation, signature, ports and exact operand geometry
    # before this key can probe a warm memo or reach a publisher.
    if action_admission is None:
        results._validate_key(key)
    else:
        results._validate_key(key, action_admission=action_admission)
    return key


def probe_causal_result(
    results: CompletedResultArena,
    action: FieldCellActionID,
    input_tile: TileID,
    state: CausalInputState,
    wiring: ResultWiring,
    *,
    action_admission: object | None = None,
) -> tuple[PoweredResultKey, ResultLease | None]:
    """Construct and probe atomically; the lookup validates before memo access.

    Unlike a separately published key, this envelope never escapes before the
    validating lookup. Public lookup and completed-result publication retain
    their full validation paths.
    """
    key = _causal_result_key(
        results, action, input_tile, state, wiring, action_admission=action_admission
    )
    results.ledger.bump(_execution_keys.TILE_CAUSAL_RESULT_PROBE_REQUESTS)
    found = lookup_causal_result(results, key, action_admission=action_admission)
    return key, found


def lookup_causal_result(
    results: CompletedResultArena,
    key: PoweredResultKey,
    *,
    action_admission: object | None = None,
) -> ResultLease | None:
    """Probe the existing result memo; no causal continuation is retained."""
    if type(results) is not CompletedResultArena:
        raise TypeError("causal lookup requires the shared result arena")
    if type(key) is not PoweredResultKey:
        raise TypeError("causal lookup requires a powered-result key")
    if action_admission is None:
        return results.lookup(key)
    return results.lookup(key, _action_admission=action_admission)


def primitive_causal_semantics(
    results: CompletedResultArena,
    action: FieldCellActionID,
    input_tile: TileID,
    output: TileID,
    ports: PrimitiveCausalPorts,
    wiring: ResultWiring,
    occurrence: TemporalCocycle,
) -> ResultSemantics:
    """Derive complete primitive semantics around an already computed output.

    ``occurrence`` is explicit because Collatz event observations are not a
    property of the temporal action alone.  The caller must aggregate them
    while executing the exact causal macro; silently defaulting them would make
    otherwise identical output tiles return the wrong weight on a memo hit.
    """
    if type(results) is not CompletedResultArena:
        raise TypeError("primitive causal semantics require the shared result arena")
    if type(ports) is not PrimitiveCausalPorts:
        raise TypeError("primitive causal semantics require finite port states")
    if type(occurrence) is not TemporalCocycle:
        raise TypeError("primitive causal semantics require an occurrence cocycle")
    key = causal_result_key(results, action, input_tile, ports, wiring)
    authority = cast("PrimitiveTileKernelAdapter", results.action_authority)
    compiler = getattr(authority, "_compile_interface", None)
    observer = getattr(authority, "_observe", None)
    cocycle_hook = getattr(authority, "action_cocycle", None)
    if not callable(compiler) or not callable(observer) or not callable(cocycle_hook):
        raise TypeError("primitive causal semantics require executable interface laws")
    interface = compiler(action, input_tile, wiring)
    if type(interface) is not LocalInterfaceID:
        raise TypeError("primitive causal compiler returned another interface sort")
    outgoing_left = observer(interface, "boundary_left", key.ports)
    outgoing_right = observer(interface, "boundary_right", key.ports)
    if type(outgoing_left) is not int or type(outgoing_right) is not int:
        raise TypeError("primitive causal observer returned a non-integer port")
    outgoing = outgoing_left, outgoing_right
    action_weight = cocycle_hook(action)
    if type(action_weight) is not TemporalCocycle:
        raise TypeError("primitive action returned another cocycle sort")
    output_node = results.tiles.resolve(output)
    return ResultSemantics(
        interface,
        outgoing,
        action_weight.physical_ticks + occurrence.physical_ticks,
        action_weight.event_weight + occurrence.event_weight,
        action_weight.frame_shift + occurrence.frame_shift,
        relative_extent=output_node.extent,
        observed_input_ports=ports.ports,
    )


def publish_causal_result(
    results: CompletedResultArena,
    key: PoweredResultKey,
    output: TileID,
    semantics: ResultSemantics,
) -> ResultLease:
    """Atomically publish exact output and its complete outgoing semantics.

    Input prefixes live in ``key.boundaries`` and therefore refer to the input
    alphabet/coordinate space.  ``semantics.outgoing_boundaries`` are validated
    against ``output`` by :class:`CompletedResultArena`; copying input operands
    into that field is invalid unless they are also genuine output-space views.
    """
    if type(results) is not CompletedResultArena:
        raise TypeError("causal publication requires the shared result arena")
    if type(key) is not PoweredResultKey:
        raise TypeError("causal publication requires a powered-result key")
    if type(output) is not TileID:
        raise TypeError("causal publication requires a scoped output tile")
    if type(semantics) is not ResultSemantics:
        raise TypeError("causal publication requires complete result semantics")
    return results.publish(key, semantics.completed(output))


def publish_causal_completed(
    results: CompletedResultArena,
    key: PoweredResultKey,
    completed: CausalCompletedOutput,
) -> ResultLease:
    """Publish the typed task result without retaining its derivation frames."""
    if type(completed) is not CausalCompletedOutput:
        raise TypeError("causal publication requires a completed output task")
    semantics = completed.semantics
    if completed.incoming_ports is not None:
        if semantics.observed_input_ports not in (None, completed.incoming_ports):
            raise ValueError("causal task inputs disagree with completed semantics")
        semantics = replace(semantics, observed_input_ports=completed.incoming_ports)
    return publish_causal_result(results, key, completed.output, semantics)


def _full_boundary_tile(
    results: CompletedResultArena,
    boundaries: BoundaryTileOperands,
    *,
    label: str,
) -> TileID:
    left, right = boundaries.left, boundaries.right
    if left is None or right is None or left.tile != right.tile:
        raise ValueError(f"{label} requires two views of one exact tile")
    node = results.tiles.resolve(left.tile)
    if (
        left.relative_origin != 0
        or right.relative_origin != 0
        or left.relative_extent != node.width
        or right.relative_extent != node.width
        or left.source_offset != 0
        or right.source_offset != 0
        or left.orientation != 0
        or right.orientation != 1
    ):
        raise ValueError(f"{label} requires complete forward/backward tile views")
    return left.tile


def combine_causal_outputs(
    results: CompletedResultArena,
    action: FieldCellActionID,
    output: TileID,
    left: CausalCompletedOutput,
    right: CausalCompletedOutput,
    wiring: ResultWiring,
    *,
    producer_output: TileID | None = None,
) -> CausalCompletedOutput:
    """Spatially combine exact causal children and final-stage interfaces.

    The caller has already joined the exact output children.  This operation
    composes only the bounded final-primitive interfaces and result metadata;
    it never requests an intermediate temporal tile or scans either child.
    """
    if type(results) is not CompletedResultArena:
        raise TypeError("causal composition requires the shared result arena")
    if (
        type(left) is not CausalCompletedOutput
        or type(right) is not CausalCompletedOutput
    ):
        raise TypeError("causal composition requires completed child outputs")
    left.__post_init__()
    right.__post_init__()
    results._validate_action_wiring(action, wiring)
    parent = results.tiles.resolve(output)
    if parent.left != left.output or parent.right != right.output:
        raise ValueError("causal output does not contain its canonical children")
    if left.semantics.physical_ticks != right.semantics.physical_ticks:
        raise ValueError("causal spatial children have different temporal spans")
    if left.semantics.frame_shift != right.semantics.frame_shift:
        raise ValueError("causal spatial children have different frame shifts")
    results._validate_ports(wiring.signature, left.semantics.outgoing_ports)
    results._validate_ports(wiring.signature, right.semantics.outgoing_ports)
    if left.incoming_ports is None or right.incoming_ports is None:
        raise ValueError("causal spatial children omitted their incoming states")
    results._validate_ports(wiring.signature, left.incoming_ports)
    results._validate_ports(wiring.signature, right.incoming_ports)
    if (
        left.semantics.outgoing_ports[0] != right.incoming_ports[0]
        or right.semantics.outgoing_ports[1] != left.incoming_ports[1]
    ):
        raise ValueError("causal child exits disagree at the spatial midpoint")
    incoming_ports = (left.incoming_ports[0], right.incoming_ports[1])
    outgoing = (
        right.semantics.outgoing_ports[0],
        left.semantics.outgoing_ports[1],
    )
    left_fusion, right_fusion = left.semantics.fusion, right.semantics.fusion
    if (left_fusion is None) != (right_fusion is None):
        raise ValueError("causal spatial children disagree on temporal-edge semantics")
    output_boundaries = BoundaryTileOperands(
        BoundaryTileView(output, 0, parent.width, 0, 0),
        BoundaryTileView(output, 0, parent.width, 1, 0),
    )
    fusion: FusedBoundaryContract | None = None
    if left_fusion is not None and right_fusion is not None:
        if type(producer_output) is not TileID:
            raise ValueError(
                "fused causal composition requires its exact producer output"
            )
        for bound in (
            left_fusion.producer,
            left_fusion.consumer,
            right_fusion.producer,
            right_fusion.consumer,
        ):
            results._validate_bound_port_allocations(bound)
            if len(bound.ports) != 2:
                raise ValueError("causal edge composition requires two directed ports")
        if (
            left_fusion.producer.wiring != right_fusion.producer.wiring
            or left_fusion.consumer.wiring != right_fusion.consumer.wiring
        ):
            raise ValueError("causal spatial children have different edge wiring")
        if (
            left.semantics.outgoing_ports != left_fusion.consumer.ports
            or right.semantics.outgoing_ports != right_fusion.consumer.ports
        ):
            raise ValueError("causal child exits disagree with consumer edge semantics")
        left_producer = _full_boundary_tile(
            results,
            left_fusion.producer.boundaries,
            label="left producer edge",
        )
        right_producer = _full_boundary_tile(
            results,
            right_fusion.producer.boundaries,
            label="right producer edge",
        )
        producer_parent = results.tiles.resolve(producer_output)
        if (
            producer_parent.left != left_producer
            or producer_parent.right != right_producer
        ):
            raise ValueError("producer output does not contain its canonical children")
        producer_boundaries = BoundaryTileOperands(
            BoundaryTileView(producer_output, 0, producer_parent.width, 0, 0),
            BoundaryTileView(producer_output, 0, producer_parent.width, 1, 0),
        )
        producer = BoundPorts(
            (
                right_fusion.producer.ports[0],
                left_fusion.producer.ports[1],
            ),
            left_fusion.producer.wiring,
            producer_boundaries,
        )
        consumer = BoundPorts(
            (
                right_fusion.consumer.ports[0],
                left_fusion.consumer.ports[1],
            ),
            left_fusion.consumer.wiring,
            output_boundaries,
        )
        results._validate_bound_port_allocations(producer)
        results._validate_bound_port_allocations(consumer)
        fusion = FusedBoundaryContract(producer, consumer)

    authority = cast("PrimitiveTileKernelAdapter", results.action_authority)
    record = authority._action(action)
    from number_compiler.hashlife.execution.tile_causal_interfaces import (
        combine_local_interfaces,
    )

    interface = combine_local_interfaces(
        results,
        action,
        left.semantics.outgoing,
        right.semantics.outgoing,
        wiring,
    )
    if record.spatial_events_add:
        events = left.semantics.event_weight + right.semantics.event_weight
    else:
        if left.semantics.event_weight != right.semantics.event_weight:
            raise ValueError("causal spatial children have different event weights")
        events = left.semantics.event_weight
    from number_compiler.hashlife.execution.tile_physical_support import (
        spatial_physical_support,
    )

    return CausalCompletedOutput(
        output,
        ResultSemantics(
            interface,
            outgoing,
            left.semantics.physical_ticks,
            events,
            left.semantics.frame_shift,
            relative_extent=parent.extent,
            outgoing_boundaries=output_boundaries,
            fusion=fusion,
            physical_support=spatial_physical_support(
                left.semantics.physical_support,
                right.semantics.physical_support,
            ),
        ),
        incoming_ports,
    )


__all__ = [
    "CausalCompletedOutput",
    "CausalInputState",
    "CompositeCausalPrefixes",
    "PrimitiveCausalPorts",
    "cached_causal_output",
    "causal_result_key",
    "combine_causal_outputs",
    "lookup_causal_result",
    "primitive_causal_semantics",
    "probe_causal_result",
    "publish_causal_completed",
    "publish_causal_result",
]
