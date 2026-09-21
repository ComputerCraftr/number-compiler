"""Pure validation for completed-result ports and exact boundary operands."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    FusedInterfaceKey,
    PoweredResultKey,
)
from number_compiler.hashlife.tiles.tiles import TileAlphabetID, TileArena, TileID
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena


def validate_output_region(
    region: tuple[int, int] | None,
    *,
    input_level: int | None = None,
) -> None:
    """A region is dyadic source geometry, never a list of output observations."""
    if region is None:
        return
    if (
        type(region) is not tuple
        or len(region) != 2
        or any(type(n) is not int for n in region)
    ):
        raise TypeError("causal output region requires two exact integers")
    origin, level = region
    if origin < 0 or level < 0:
        raise ValueError("causal output region cannot be negative")
    if input_level is not None and level > input_level:
        raise ValueError("causal output region exceeds its input level")
    if origin and level >= (origin & -origin).bit_length():
        raise ValueError("causal output region must be dyadically aligned")
    if input_level is not None and origin.bit_length() > input_level:
        raise ValueError("causal output region exceeds its input tile")


def normalize_output_region(
    tiles: TileArena, key: PoweredResultKey
) -> PoweredResultKey:
    """Use the existing full-result binding for a whole-input region."""
    from dataclasses import replace

    level = tiles.resolve(key.input).level
    validate_output_region(key.region, input_level=level)
    if key.region == (0, level):
        return replace(key, region=None)
    return key


def validated_action_signature(
    arena: CompletedResultArena, action: FieldCellActionID
) -> PortSignatureID:
    """Deeply admit an action and obtain its signature in one authority call.

    This is request-local validation, not memoized admission. Authorities which
    do not offer the combined operation retain the separate validation path.
    """
    if type(action) is not FieldCellActionID:
        raise TypeError("powered result requires a scoped field action")
    if arena._validated_signature_for is None:
        arena._validate_action(action)
        signature = arena._signature_for(action)
    else:
        admitted = arena._validated_signature_for(action)
        if type(admitted) is not PortSignatureID:
            raise TypeError(
                "combined action validation returned another signature sort"
            )
        signature = admitted
    arena.interfaces.interface(signature)
    return signature


def validate_fused_edge(arena: CompletedResultArena, key: FusedInterfaceKey) -> None:
    """Check an explicit temporal edge without compiling or observing it.

    Opaque authorities may admit an atomic fused operation without exposing a
    decomposition. An authority exposing temporal children must supply that
    edge in every request; total-exponent equality cannot transport its ports.
    """
    if (key.before is None) != (key.after is None):
        raise ValueError("fused edge requires both temporal children")
    children_hook = getattr(arena.action_authority, "action_children", None)
    if key.before is None:
        if children_hook is not None:
            raise ValueError(
                "decomposed fused requests require explicit temporal children"
            )
    else:
        if (
            type(key.before) is not FieldCellActionID
            or type(key.after) is not FieldCellActionID
        ):
            raise TypeError("fused edge requires scoped temporal children")
        before_signature = validated_action_signature(arena, key.before)
        after_signature = validated_action_signature(arena, key.after)
        if (
            not callable(children_hook)
            or getattr(children_hook, "__self__", None) is not arena.action_authority
        ):
            raise ValueError("action authority cannot validate this temporal edge")
        children = cast(
            Callable[
                [FieldCellActionID], tuple[FieldCellActionID, FieldCellActionID] | None
            ],
            children_hook,
        )(key.action)
        if children != (key.before, key.after):
            raise ValueError(
                "fused temporal decomposition requires verified port transport"
            )
        if (
            before_signature != key.producer_context.signature
            or after_signature != key.wiring.signature
        ):
            raise ValueError(
                "fused temporal children have different interface signatures"
            )
    validate_boundary_operands(arena.tiles, key.consumer_boundaries)
    for tile in key.consumer_boundaries.tile_ids():
        if key.after is not None and arena._validate_input is not None:
            arena._validate_input(key.after, tile)
        elif (
            arena.tiles.resolve(tile).alphabet
            != arena.tiles.resolve(key.input).alphabet
        ):
            raise ValueError(
                "consumer boundary tile has another alphabet interpretation"
            )


def validate_fused_request(arena: CompletedResultArena, key: FusedInterfaceKey) -> None:
    if type(key) is not FusedInterfaceKey:
        raise TypeError("expected a fused-interface key")
    arena._validate_base(key.action, key.input, key.wiring)
    arena._validate_boundaries(key.boundaries, key.input)
    if arena._validate_fused_action is None:
        raise ValueError("action authority does not admit fused interfaces")
    arena._validate_fused_action(key.action)
    validate_fused_edge(arena, key)
    producer_wiring = key.producer_wiring
    if type(producer_wiring) is not ResultWiring:
        raise TypeError("fused producer requires normalized wiring")
    producer_wiring.__post_init__()
    producer_signature = arena.interfaces.interface(producer_wiring.signature)
    if producer_wiring.orientation not in producer_signature.orientations:
        raise ValueError("fused producer orientation lies outside its signature")
    if producer_wiring.phase >= producer_signature.phase_count:
        raise ValueError("fused producer phase lies outside its signature")
    if arena._validate_fused_wiring is None:
        if producer_wiring != key.wiring:
            raise ValueError(
                "action authority does not admit heterogeneous fused wiring"
            )
    else:
        arena._validate_fused_wiring(key.action, producer_wiring, key.wiring)
    arena._validate_ports(producer_wiring.signature, key.ports)


def validate_fusion_contexts(
    arena: CompletedResultArena,
    action: FieldCellActionID,
    fusion: FusedBoundaryContract,
    consumer: BoundPorts,
    expected: TileID,
    *,
    counted: bool = True,
    output: bool = False,
    action_admission: object | None = None,
) -> int:
    """Validate each temporal side in its own input or output alphabet."""
    if type(fusion) is not FusedBoundaryContract:
        raise TypeError("execution fusion requires an exact boundary contract")
    fusion.__post_init__()
    if fusion.consumer != consumer:
        raise ValueError("fusion consumer disagrees with the execution request")
    if action_admission is None:
        if arena._validate_fused_action is None:
            raise ValueError("action authority does not admit fused interfaces")
        arena._validate_fused_action(action)
        if arena._validate_fused_wiring is None:
            if fusion.producer.wiring != fusion.consumer.wiring:
                raise ValueError(
                    "action authority does not admit heterogeneous fused wiring"
                )
        else:
            arena._validate_fused_wiring(
                action, fusion.producer.wiring, fusion.consumer.wiring
            )
        children_hook = getattr(arena.action_authority, "action_children", None)
        children = None
    else:
        from number_compiler.resources.causal_workspace import (
            admitted_action_metadata,
        )

        _signature, _kernel, record = admitted_action_metadata(
            action_admission, arena.action_authority, action
        )
        children_hook = None
        children = record.children
        if children is None or any(
            wiring.orientation or wiring.phase
            for wiring in (fusion.producer.wiring, fusion.consumer.wiring)
        ):
            raise ValueError("fused wiring requires its admitted temporal edge")
    if children_hook is not None:
        if (
            not callable(children_hook)
            or getattr(children_hook, "__self__", None) is not arena.action_authority
        ):
            raise ValueError("fusion requires a bound temporal-edge authority")
        children = cast(
            Callable[
                [FieldCellActionID], tuple[FieldCellActionID, FieldCellActionID] | None
            ],
            children_hook,
        )(action)
        if type(children) is not tuple or len(children) != 2:
            raise ValueError("fusion requires two temporal children")
    domain_validator = arena._validate_output if output else arena._validate_input
    visits = 0
    for side, context in enumerate((fusion.producer, fusion.consumer)):
        child = None
        if children is not None:
            child = children[side]
            if type(child) is not FieldCellActionID:
                raise TypeError("fusion requires scoped temporal children")
            if action_admission is None:
                child_signature = validated_action_signature(arena, child)
            else:
                child_signature, _kernel, _record = admitted_action_metadata(
                    action_admission, arena.action_authority, child
                )
            if child_signature != context.signature:
                raise ValueError("fusion child has another interface signature")
        if child is not None and (
            domain_validator is not None or action_admission is not None
        ):
            visits += validate_bound_context(
                arena.interfaces, arena.tiles, context, None
            )
            for tile in context.boundaries.tile_ids():
                if action_admission is None:
                    assert domain_validator is not None
                    domain_validator(child, tile)
                else:
                    from number_compiler.hashlife.tiles.completed_result_validation import (
                        _validate_admitted_input,
                    )

                    _validate_admitted_input(
                        arena,
                        child,
                        tile,
                        action_admission,
                        output=output,
                    )
        else:
            visits += validate_bound_context(
                arena.interfaces,
                arena.tiles,
                context,
                arena.tiles.resolve(expected).alphabet,
            )
    if counted:
        arena.ledger.bump("completed_result_port_validation_requests", 2)
        arena.ledger.bump("completed_result_port_validation_visits", visits)
    return visits


def validate_ports_readonly(
    interfaces: DiamondQuotientArena,
    signature: PortSignatureID,
    values: tuple[int, ...],
    *,
    ledger: ResourceLedger | None = None,
) -> int:
    """Validate one finite assignment without executing a semantic function."""
    if type(values) is not tuple or any(type(value) is not int for value in values):
        raise TypeError("result ports require exact immutable integers")
    declaration = interfaces.interface(signature)
    if len(values) != len(declaration.inputs):
        raise ValueError("result ports do not match their signature")
    assignment: dict[tuple[int, int, str, int], int] = {}
    for port, value in zip(declaration.inputs, values, strict=True):
        if not 0 <= value < port.cardinality:
            raise ValueError("result port lies outside its finite domain")
        variable = port.variable
        assignment[variable.time, variable.side, variable.role, variable.bit] = value
    node = interfaces.functions.resolve(declaration.admissible)
    if ledger is not None:
        if type(ledger) is not ResourceLedger or ledger is not interfaces.ledger:
            raise ValueError("port validation ledger belongs to another index")
        ledger.bump("completed_result_port_validation_requests")
    visits = 0
    while node.variable is not None:
        variable = node.variable
        PortVariable.__post_init__(variable)
        # Only the base coordinates select an assignment. Constructing and
        # validating a new PortVariable for every decision bit repeats work on
        # an already admitted signature and decision DAG.
        base = variable.time, variable.side, variable.role, 0
        node = interfaces.functions.nodes[
            node.high if (assignment[base] >> variable.bit) & 1 else node.low
        ]
        visits += 1
        if ledger is not None:
            ledger.bump("completed_result_port_validation_visits")
    terminal = node.terminal
    if terminal is None or terminal.kind != "atom" or terminal.value != 1:
        raise ValueError("result ports are inadmissible")
    return visits


def validate_boundary_operands(
    tiles: TileArena,
    boundaries: BoundaryTileOperands,
    *,
    expected_alphabet: TileAlphabetID | None = None,
) -> None:
    """Validate live boundary views and their exact cell interpretation."""
    if type(tiles) is not TileArena:
        raise TypeError("boundary validation requires a tile arena")
    if type(boundaries) is not BoundaryTileOperands:
        raise TypeError("result request requires exact boundary operands")
    boundaries.__post_init__()
    if expected_alphabet is not None:
        if type(expected_alphabet) is not TileAlphabetID:
            raise TypeError("boundary validation requires a tile alphabet ID")
        tiles.alphabet(expected_alphabet)
    for view in (boundaries.left, boundaries.right):
        if view is None:
            continue
        if type(view) is not BoundaryTileView:
            raise TypeError("boundary operands require exact boundary views")
        record = tiles.resolve(view.tile)
        if expected_alphabet is not None and record.alphabet != expected_alphabet:
            raise ValueError("boundary tile has another alphabet interpretation")
        if view.source_offset > record.width:
            raise ValueError("boundary source offset exceeds its exact tile")
        if view.source_offset + view.relative_extent > record.width:
            raise ValueError("boundary extent exceeds its exact tile")


def validate_bound_context(
    interfaces: DiamondQuotientArena,
    tiles: TileArena,
    context: BoundPorts,
    expected: TileAlphabetID | None,
    *,
    ledger: ResourceLedger | None = None,
) -> int:
    """Validate a full contract, optionally deferring its work accounting."""
    if type(context) is not BoundPorts:
        raise TypeError("execution contract requires exact bound ports")
    context.__post_init__()
    declaration = interfaces.interface(context.signature)
    if context.wiring.orientation not in declaration.orientations:
        raise ValueError("bound-port orientation lies outside its signature")
    if context.wiring.phase >= declaration.phase_count:
        raise ValueError("bound-port phase lies outside its signature")
    validate_boundary_operands(tiles, context.boundaries, expected_alphabet=expected)
    return validate_ports_readonly(
        interfaces, context.signature, context.ports, ledger=ledger
    )


__all__ = [
    "validate_bound_context",
    "validate_boundary_operands",
    "validate_ports_readonly",
]
