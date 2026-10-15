"""Read-only validation for retained tile-runtime requests and observations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_ports import BoundPorts
from number_compiler.hashlife.tiles.tile_result_records import (
    CausalInterfaceKey,
    CompletedInterfaceResult,
    PoweredResultKey,
    RootMatchResult,
    SourceRootMatchKey,
    causal_interface_snapshot,
)
from number_compiler.hashlife.tiles.tiles import TileAlphabet, TileID
from number_compiler.resources.tile_alphabet_contract import (
    CANONICAL_TILE_ALPHABET_VERSION,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


def valid_ports(
    scheduler: TileScheduler,
    signature: PortSignatureID,
    values: object,
) -> bool:
    """Check a finite assignment by walking its published admissibility DAG."""
    if type(values) is not tuple or any(type(value) is not int for value in values):
        return False
    try:
        declaration = scheduler.results.interfaces.interface(signature)
        if len(values) != len(declaration.inputs):
            return False
        assignment: dict[PortVariable, int] = {}
        for port, value in zip(declaration.inputs, values, strict=True):
            if not 0 <= value < port.cardinality:
                return False
            assignment[port.variable] = value
        functions = scheduler.results.interfaces.functions
        node = functions.resolve(declaration.admissible)
        while node.variable is not None:
            variable = node.variable
            base = PortVariable(variable.time, variable.side, variable.role, 0)
            node = functions.nodes[
                node.high if (assignment[base] >> variable.bit) & 1 else node.low
            ]
        terminal = node.terminal
        return terminal is not None and terminal.kind == "atom" and terminal.value == 1
    except (TypeError, ValueError, KeyError, AttributeError, IndexError):
        return False


def valid_boundaries(
    scheduler: TileScheduler,
    boundaries: object,
    expected: TileID,
) -> bool:
    if type(boundaries) is not BoundaryTileOperands:
        return False
    try:
        alphabet = scheduler.tiles.resolve(expected).alphabet
    except (TypeError, ValueError, KeyError, AttributeError, IndexError):
        return False
    for view in (boundaries.left, boundaries.right):
        if view is None:
            continue
        if type(view) is not BoundaryTileView:
            return False
        try:
            view.__post_init__()
            record = scheduler.tiles.resolve(view.tile)
            if (
                view.source_offset > record.width
                or view.source_offset + view.relative_extent > record.width
                or record.alphabet != alphabet
            ):
                return False
        except (TypeError, ValueError, KeyError, AttributeError, IndexError):
            return False
    return True


def valid_request(scheduler: TileScheduler, key: PoweredResultKey) -> bool:
    """Validate one retained request without executing an output observation."""
    if type(key) is not PoweredResultKey:
        return False
    try:
        key.wiring.__post_init__()
        results = scheduler.results
        results._validate_action(key.action)
        expected = results._signature_for(key.action)
        declaration = results.interfaces.interface(expected)
        if (
            key.wiring.signature != expected
            or key.wiring.orientation not in declaration.orientations
            or not 0 <= key.wiring.phase < declaration.phase_count
        ):
            return False
        scheduler.tiles.resolve(key.input)
        if results._validate_input is not None:
            results._validate_input(key.action, key.input)
        if not valid_boundaries(scheduler, key.boundaries, key.input):
            return False
        valid = valid_ports(scheduler, expected, key.ports)
        if key.fusion is None:
            return valid
        fusion = key.fusion
        fusion.__post_init__()
        if fusion.consumer != BoundPorts(key.ports, key.wiring, key.boundaries):
            return False
        for context in (fusion.producer, fusion.consumer):
            context.__post_init__()
            interface = results.interfaces.interface(context.signature)
            valid &= (
                context.wiring.orientation in interface.orientations
                and 0 <= context.wiring.phase < interface.phase_count
                and valid_ports(scheduler, context.signature, context.ports)
                and valid_boundaries(scheduler, context.boundaries, key.input)
            )
        if results._validate_fused_action is None:
            return False
        results._validate_fused_action(key.action)
        if results._validate_fused_wiring is None:
            valid &= fusion.producer.wiring == fusion.consumer.wiring
        else:
            results._validate_fused_wiring(
                key.action,
                fusion.producer.wiring,
                fusion.consumer.wiring,
            )
        return valid
    except (TypeError, ValueError, KeyError, AttributeError, IndexError):
        return False


def valid_causal_interface_record(
    adapter: PrimitiveTileKernelAdapter,
    scheduler: TileScheduler | None,
    key: CausalInterfaceKey,
    result: CompletedInterfaceResult,
) -> bool:
    """Independently check a sealed causal observation without reducing semantics."""
    try:
        results = adapter.results
        if results is None:
            return False
        result.__post_init__()
        observed_reverse = key.observation == "reverse-output-carry"
        valid = (
            type(key.observation) is str
            and key.observation in ("interface", "reverse-output-carry")
            and observed_reverse == (result.bound_reverse_output is not None)
            and result._publication_owner is results._interface_publication_seal
            and result._publication_snapshot == causal_interface_snapshot(key, result)
            and result.level == adapter.tiles.resolve(key.input).level
            and adapter.quotients.resolve(result.interface).signature
            == key.wiring.signature
        )
        if scheduler is None:
            return False
        valid &= valid_request(
            scheduler,
            PoweredResultKey(
                key.action,
                key.input,
                key.ports,
                key.wiring,
                key.boundaries,
                key.fusion,
            ),
        )
        if result.bound_reverse_output is not None:
            result.bound_reverse_output.__post_init__()
        return valid
    except (TypeError, ValueError, KeyError, AttributeError, IndexError):
        return False


def valid_source_root_match_record(
    adapter: PrimitiveTileKernelAdapter,
    key: SourceRootMatchKey,
    result: RootMatchResult,
) -> bool:
    """Check a sealed two-phase root summary from immutable retained scalars."""
    try:
        results = adapter.results
        if results is None:
            return False
        key.__post_init__()
        result.__post_init__()
        source = adapter.tiles.resolve(key.input)
        alphabet = adapter.tiles.alphabet(source.alphabet)
        expected = TileAlphabet(
            3,
            2,
            2,
            2,
            "unsigned-radix-cell-with-explicit-blank",
            CANONICAL_TILE_ALPHABET_VERSION,
        )
        return (
            alphabet == expected
            and result.level == source.level
            and result._publication_owner is results._interface_publication_seal
            and result._publication_snapshot
            == (
                key.input.owner,
                key.input.kind,
                key.input.local_id,
                result.level,
                result.phase0_first_mismatch,
                result.phase1_first_mismatch,
            )
        )
    except (TypeError, ValueError, KeyError, AttributeError, IndexError):
        return False


__all__ = [
    "valid_boundaries",
    "valid_causal_interface_record",
    "valid_ports",
    "valid_request",
    "valid_source_root_match_record",
]
