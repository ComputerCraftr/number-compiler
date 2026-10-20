"""Output-independent interface payloads for causal width descent.

Payloads are transient scheduler values.  Canonical semantic functions remain
owned by ``DiamondQuotientArena`` and spatial aliases by
``CompletedResultArena``; this module owns no memo, callback, or exact output.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import is_runtime_instance

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.resources.causal_workspace import CausalActionAdmission

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.tile_causal_results import (
    CausalCompletedOutput,
    PrimitiveCausalPorts,
    require_causal_authority,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    LocalInterfaceID,
    MacroComponents,
)
from number_compiler.hashlife.tiles.ordered_boolean_support import OrderedBooleanSupport
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import (
    CompletedResult,
    SpatialInterfaceKey,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileID

_BOUND_OUTPUT_SEAL = object()
_BOUND_OUTPUT_REQUEST_SEAL = object()


def _bound_output_snapshot(
    payload: CausalInterfacePayload,
    value: ReverseBoundOutput,
) -> tuple[object, ...]:
    """Bind a finite output proof to one immutable occurrence payload."""
    return _bound_output_snapshot_values(
        payload.interface,
        payload.incoming_ports,
        payload.outgoing_ports,
        payload.level,
        payload.active,
        payload.physical_ticks,
        payload.event_weight,
        payload.frame_shift,
        value,
    )


def _bound_output_snapshot_values(
    interface: LocalInterfaceID,
    incoming_ports: tuple[int, int],
    outgoing_ports: tuple[int, int],
    level: int,
    active: bool,
    physical_ticks: int,
    event_weight: int,
    frame_shift: int,
    value: ReverseBoundOutput,
) -> tuple[object, ...]:
    return (
        interface,
        incoming_ports,
        outgoing_ports,
        level,
        active,
        physical_ticks,
        event_weight,
        frame_shift,
        value.left,
        value.right,
    )


@dataclass(frozen=True, slots=True)
class CausalInterfacePayload:
    """Bounded final-stage behavior for one spatial macrocell."""

    interface: LocalInterfaceID
    incoming_ports: tuple[int, int]
    outgoing_ports: tuple[int, int]
    level: int
    active: bool
    physical_ticks: int = 0
    event_weight: int = 0
    frame_shift: int = 0
    physical_support: OrderedBooleanSupport | None = field(default=None, kw_only=True)
    bound_reverse_output: ReverseBoundOutput | None = field(default=None, kw_only=True)
    _bound_output_owner: object | None = field(default=None, kw_only=True, repr=False)
    _bound_output_snapshot: tuple[object, ...] | None = field(
        default=None, kw_only=True, repr=False
    )
    _bound_output_request_owner: object | None = field(
        default=None, kw_only=True, repr=False
    )
    _bound_output_request_snapshot: tuple[object, ...] | None = field(
        default=None, kw_only=True, repr=False
    )

    def bound_request_matches(self, snapshot: tuple[object, ...]) -> bool:
        return self._bound_output_request_snapshot == snapshot

    def __post_init__(self) -> None:
        if type(self.interface) is not LocalInterfaceID:
            raise TypeError("causal interface payload requires a local interface ID")
        for name, ports in (
            ("incoming", self.incoming_ports),
            ("outgoing", self.outgoing_ports),
        ):
            if (
                type(ports) is not tuple
                or len(ports) != 2
                or any(type(value) is not int for value in ports)
            ):
                raise TypeError(f"causal {name} ports require two exact integers")
        if type(self.level) is not int:
            raise TypeError("causal interface level requires an exact integer")
        if self.level < 0:
            raise ValueError("causal interface level cannot be negative")
        if type(self.active) is not bool:
            raise TypeError("causal interface activity requires an exact Boolean")
        if any(
            type(value) is not int
            for value in (
                self.physical_ticks,
                self.event_weight,
                self.frame_shift,
            )
        ):
            raise TypeError("causal interface weights require exact integers")
        if self.physical_ticks < 0 or self.event_weight < 0:
            raise ValueError("causal interface weights cannot be negative")
        if self.physical_support is not None:
            if not is_runtime_instance(self.physical_support, OrderedBooleanSupport):
                raise TypeError("causal interface has another shadow-support sort")
            self.physical_support.owner.validate(self.physical_support)
            if self.physical_support.ticks and (
                self.physical_support.ticks != self.physical_ticks
                or self.physical_support.true_count != self.event_weight
            ):
                raise ValueError("causal support disagrees with interface weights")
        if self.bound_reverse_output is not None:
            if type(self.bound_reverse_output) is not ReverseBoundOutput:
                raise TypeError("causal interface has another active behavior sort")
            self.bound_reverse_output.__post_init__()
            if self._bound_output_owner is not _BOUND_OUTPUT_SEAL or (
                self._bound_output_snapshot
                != _bound_output_snapshot(self, self.bound_reverse_output)
            ):
                raise ValueError("causal active behavior has no occurrence proof")
            if (self._bound_output_request_owner is None) != (
                self._bound_output_request_snapshot is None
            ) or self._bound_output_request_owner not in (
                None,
                _BOUND_OUTPUT_REQUEST_SEAL,
            ):
                raise ValueError("causal active behavior has no request proof")
        elif (
            self._bound_output_owner is not None
            or self._bound_output_snapshot is not None
        ):
            raise ValueError("causal interface retains an orphan active proof")
        elif (
            self._bound_output_request_owner is not None
            or self._bound_output_request_snapshot is not None
        ):
            raise ValueError("causal interface retains an orphan request proof")


@dataclass(frozen=True, slots=True)
class CausalLeafInterface:
    """One emitted symbol and its completed causal interface payload."""

    symbol: int
    payload: CausalInterfacePayload


def attach_bound_reverse_output(
    payload: CausalInterfacePayload,
    output: ReverseBoundOutput,
) -> CausalInterfacePayload:
    """Seal one internally derived output summary to its occurrence payload."""
    if type(payload) is not CausalInterfacePayload:
        raise TypeError("active behavior requires a causal interface payload")
    if type(output) is not ReverseBoundOutput:
        raise TypeError("active behavior requires a bound reverse output")
    payload.__post_init__()
    output.__post_init__()
    # The proof includes every occurrence scalar, so an issued finite summary
    # cannot be transplanted onto another request with the same radix.
    return CausalInterfacePayload(
        payload.interface,
        payload.incoming_ports,
        payload.outgoing_ports,
        payload.level,
        payload.active,
        payload.physical_ticks,
        payload.event_weight,
        payload.frame_shift,
        physical_support=payload.physical_support,
        bound_reverse_output=output,
        _bound_output_owner=_BOUND_OUTPUT_SEAL,
        _bound_output_snapshot=_bound_output_snapshot_values(
            payload.interface,
            payload.incoming_ports,
            payload.outgoing_ports,
            payload.level,
            payload.active,
            payload.physical_ticks,
            payload.event_weight,
            payload.frame_shift,
            output,
        ),
    )


def bind_bound_reverse_output_request(
    payload: CausalInterfacePayload,
    request_snapshot: tuple[object, ...],
) -> CausalInterfacePayload:
    """Bind an internally derived summary to its complete execution request."""
    if type(payload) is not CausalInterfacePayload:
        raise TypeError("active behavior requires a causal interface payload")
    payload.__post_init__()
    if payload.bound_reverse_output is None:
        raise ValueError("request proof requires an active output summary")
    if type(request_snapshot) is not tuple:
        raise TypeError("active behavior request proof must be immutable")
    return CausalInterfacePayload(
        payload.interface,
        payload.incoming_ports,
        payload.outgoing_ports,
        payload.level,
        payload.active,
        payload.physical_ticks,
        payload.event_weight,
        payload.frame_shift,
        physical_support=payload.physical_support,
        bound_reverse_output=payload.bound_reverse_output,
        _bound_output_owner=_BOUND_OUTPUT_SEAL,
        _bound_output_snapshot=_bound_output_snapshot(
            payload, payload.bound_reverse_output
        ),
        _bound_output_request_owner=_BOUND_OUTPUT_REQUEST_SEAL,
        _bound_output_request_snapshot=request_snapshot,
    )


def interface_payload_from_completed(
    results: CompletedResultArena,
    completed: CompletedResult,
    incoming_ports: tuple[int, ...],
) -> CausalInterfacePayload:
    """Read bounded semantics from a validated completed result without evaluation."""
    if type(completed) is not CompletedResult:
        raise TypeError("completed interface requires an exact completed result")
    completed.__post_init__()
    observed = completed.observed_input_ports
    incoming = incoming_ports if observed is None else observed
    results.validate_ports(
        results.interfaces.resolve(completed.outgoing).signature, incoming
    )
    node = results.tiles.resolve(completed.output)
    return CausalInterfacePayload(
        completed.outgoing,
        (incoming[0], incoming[1]),
        (completed.outgoing_ports[0], completed.outgoing_ports[1]),
        node.level,
        node.first_active is not None,
        completed.physical_ticks,
        completed.event_weight,
        completed.frame_shift,
        physical_support=completed.physical_support,
        bound_reverse_output=None,
    )


def _authority(results: CompletedResultArena) -> PrimitiveTileKernelAdapter:
    if type(results) is not CompletedResultArena:
        raise TypeError("causal interfaces require the shared result arena")
    return require_causal_authority(results.validated_action_authority())


def combine_local_interfaces(
    results: CompletedResultArena,
    action: FieldCellActionID,
    left: LocalInterfaceID,
    right: LocalInterfaceID,
    wiring: ResultWiring,
) -> LocalInterfaceID:
    """Compose the existing thirteen semantic channels with early reuse."""
    authority = _authority(results)
    results.validate_action_wiring(action, wiring)
    key = SpatialInterfaceKey(left, right, wiring)
    found = results.lookup_spatial_interface(key)
    if found is not None:
        return found
    record = authority.action_record(action)
    kernel = authority.kernels.kernel(record.kernel)
    from number_compiler.arithmetic.carry.reverse_port_functions import (
        MAX_CLOSED_REVERSE_BASE,
        MIN_CLOSED_REVERSE_BASE,
    )
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.arithmetic.radix_port_functions import RadixPortFunction
    from number_compiler.hashlife.tiles.interface_publication import (
        publish_spatial_quotient,
    )
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    if type(kernel.effect) is BaseBlockEffect and (
        MIN_CLOSED_REVERSE_BASE <= kernel.base <= MAX_CLOSED_REVERSE_BASE
    ):
        from number_compiler.hashlife.interfaces.tile_reverse_functions import (
            reverse_parent_components,
        )

        with authority.quotients.closed_workspace.scope("parent"):
            components = reverse_parent_components(
                authority.quotients.resolve(left).components,
                authority.quotients.resolve(right).components,
                results.ledger,
            )
            return publish_spatial_quotient(results, key, components)

    left_components = authority.quotients.resolve(left).components
    right_components = authority.quotients.resolve(right).components
    if any(type(value) is RadixPortFunction for value in left_components.functions()):
        from number_compiler.hashlife.interfaces.tile_radix_functions import (
            division_parent_components,
        )

        components = division_parent_components(
            left_components,
            right_components,
            results.ledger,
        )
        return publish_spatial_quotient(results, key, components)
    parent_functions = authority.parent_components(kernel, left, right)
    macro = MacroComponents(
        *(authority.structures.atom(component) for component in parent_functions)
    )
    if type(kernel.effect) is DigitNormalizeBlockEffect and kernel.base == 10:
        from dataclasses import replace

        from number_compiler.hashlife.interfaces.tile_reverse_sector_functions import (
            compose_reverse_sectors,
        )

        with authority.quotients.closed_workspace.scope("parent"):
            macro = replace(
                macro,
                reverse_sectors=compose_reverse_sectors(
                    authority.quotients.resolve(left).components.reverse_sectors,
                    authority.quotients.resolve(right).components.reverse_sectors,
                    ledger=results.ledger,
                ),
            )
            return publish_spatial_quotient(results, key, macro)
    interface = authority.quotients.intern(wiring.signature, macro)
    return results.publish_spatial_interface(key, interface)


def primitive_interface_payload(
    results: CompletedResultArena,
    action: FieldCellActionID,
    input_tile: TileID,
    ports: PrimitiveCausalPorts,
    wiring: ResultWiring,
    occurrence: TemporalCocycle,
    *,
    physical_support: OrderedBooleanSupport | None = None,
    action_admission: CausalActionAdmission | None = None,
) -> CausalInterfacePayload:
    """Bind one primitive action to an exact input without emitting its output."""
    authority = _authority(results)
    if type(ports) is not PrimitiveCausalPorts:
        raise TypeError("primitive causal interface requires finite ports")
    if type(occurrence) is not TemporalCocycle:
        raise TypeError("primitive causal interface requires an occurrence cocycle")
    results.validate_base(
        action,
        input_tile,
        wiring,
        action_admission=action_admission,
    )
    if action_admission is None:
        from number_compiler.hashlife.execution.tile_kernel import (
            PrimitiveTileKernelAdapter,
        )

        record = PrimitiveTileKernelAdapter.action_record(authority, action)
    else:
        from number_compiler.resources.causal_workspace import (
            admitted_action_metadata,
        )

        _signature, _kernel, record = admitted_action_metadata(
            action_admission, authority, action
        )
    if record.children is not None:
        raise ValueError("primitive causal interface requires an atomic action")
    results.validate_ports(wiring.signature, ports.ports)
    node = results.tiles.resolve(input_tile)
    interface = authority.compile_interface(action, input_tile, wiring)
    outgoing = (
        authority.observe(interface, "boundary_left", ports.ports),
        authority.observe(interface, "boundary_right", ports.ports),
    )
    active = bool(authority.observe(interface, "activity", ports.ports))
    action_weight = authority.action_cocycle(action)
    if type(action_weight) is not TemporalCocycle:
        raise TypeError("primitive causal action returned another cocycle sort")
    return CausalInterfacePayload(
        interface,
        ports.ports,
        outgoing,
        node.level,
        active,
        action_weight.physical_ticks + occurrence.physical_ticks,
        action_weight.event_weight + occurrence.event_weight,
        action_weight.frame_shift + occurrence.frame_shift,
        physical_support=physical_support,
        bound_reverse_output=None,
    )


def interface_payload_from_causal(
    results: CompletedResultArena,
    action: FieldCellActionID,
    completed: CausalCompletedOutput,
    wiring: ResultWiring,
    *,
    expected_level: int,
) -> CausalInterfacePayload:
    """Discard an exact leaf output after extracting its bounded behavior."""
    _authority(results)
    if type(completed) is not CausalCompletedOutput:
        raise TypeError("causal interface extraction requires a completed task")
    completed.__post_init__()
    if completed.incoming_ports is None:
        raise ValueError("causal interface extraction requires observed inputs")
    if type(expected_level) is not int or expected_level < 0:
        raise ValueError("causal interface extraction requires a valid level")
    node = results.tiles.resolve(completed.output)
    if node.level != expected_level:
        raise ValueError("causal interface extraction has another spatial level")
    results.validate_action_wiring(action, wiring)
    results.validate_ports(wiring.signature, completed.incoming_ports)
    results.validate_ports(wiring.signature, completed.semantics.outgoing_ports)
    # Publication already checked the interface against the exact output.
    # Its canonical summary is an observation result, not a reason to execute
    # the semantic function again on every completed-parent hit.
    active = node.first_active is not None
    return CausalInterfacePayload(
        completed.semantics.outgoing,
        completed.incoming_ports,
        (completed.semantics.outgoing_ports[0], completed.semantics.outgoing_ports[1]),
        expected_level,
        active,
        completed.semantics.physical_ticks,
        completed.semantics.event_weight,
        completed.semantics.frame_shift,
        physical_support=completed.semantics.physical_support,
        bound_reverse_output=None,
    )


def combine_causal_interfaces(
    results: CompletedResultArena,
    action: FieldCellActionID,
    left: CausalInterfacePayload,
    right: CausalInterfacePayload,
    wiring: ResultWiring,
    *,
    expected_level: int,
) -> CausalInterfacePayload:
    """Combine bounded child behavior without a final-output ``TileID``."""
    authority = _authority(results)
    if (
        type(left) is not CausalInterfacePayload
        or type(right) is not CausalInterfacePayload
    ):
        raise TypeError("causal interface composition requires bounded child payloads")
    left.__post_init__()
    right.__post_init__()
    if type(expected_level) is not int or expected_level < 1:
        raise ValueError("causal interface parent requires a positive exact level")
    if left.level != expected_level - 1 or right.level != expected_level - 1:
        raise ValueError("causal interface children have another spatial level")
    results.validate_ports(wiring.signature, left.incoming_ports)
    results.validate_ports(wiring.signature, right.incoming_ports)
    if (
        left.outgoing_ports[0] != right.incoming_ports[0]
        or right.outgoing_ports[1] != left.incoming_ports[1]
    ):
        raise ValueError("causal interface exits disagree at the spatial midpoint")
    if left.physical_ticks != right.physical_ticks:
        raise ValueError("causal interface children have different temporal spans")
    if left.frame_shift != right.frame_shift:
        raise ValueError("causal interface children have different frame shifts")
    interface = combine_local_interfaces(
        results,
        action,
        left.interface,
        right.interface,
        wiring,
    )
    incoming = (left.incoming_ports[0], right.incoming_ports[1])
    outgoing = (right.outgoing_ports[0], left.outgoing_ports[1])
    active = bool(authority.observe(interface, "activity", incoming))
    record = authority.action_record(action)
    if record.spatial_events_add:
        events = left.event_weight + right.event_weight
    else:
        if left.event_weight != right.event_weight:
            raise ValueError("causal interface children have different event weights")
        events = left.event_weight
    from number_compiler.hashlife.execution.tile_physical_support import (
        spatial_physical_support,
    )

    payload = CausalInterfacePayload(
        interface,
        incoming,
        outgoing,
        expected_level,
        active,
        left.physical_ticks,
        events,
        left.frame_shift,
        physical_support=spatial_physical_support(
            left.physical_support, right.physical_support
        ),
    )
    if left.bound_reverse_output is None or right.bound_reverse_output is None:
        return payload
    return attach_bound_reverse_output(
        payload,
        left.bound_reverse_output.then(right.bound_reverse_output, results.ledger),
    )


__all__ = [
    "CausalInterfacePayload",
    "combine_causal_interfaces",
    "combine_local_interfaces",
    "interface_payload_from_causal",
    "interface_payload_from_completed",
    "primitive_interface_payload",
]
