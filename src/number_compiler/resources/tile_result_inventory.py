"""Independent retained-store audit for completed canonical tile results."""

from __future__ import annotations

from collections.abc import Mapping
from typing import cast

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_integer_tuple,
    is_exact_object_tuple,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.formula.summary import BlockSummary
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
from number_compiler.hashlife.tiles.source_root_match_memo import (
    validate_source_root_match_value,
)
from number_compiler.hashlife.tiles.tile_behavior_memo import (
    validate_published_behavior,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_boundary_concat_memo import (
    validate_boundary_concat_value,
)
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    validate_published_causal_interface_value,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_region_memo import (
    validate_normalized_region_value,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    BehaviorBindingKey,
    BoundaryConcatKey,
    BoundaryConcatResult,
    CausalInterfaceKey,
    CompletedBehaviorClassification,
    CompletedInterfaceResult,
    CompletedResult,
    DirectedTransferKey,
    FusedInterfaceKey,
    FusedVariantKey,
    NormalizedRegionKey,
    NormalizedRegionResult,
    PoweredInterfaceKey,
    PoweredResultKey,
    ResultDependencyHead,
    ResultDependencyLinks,
    ResultDependencyMember,
    ResultVariantKey,
    ReverseBoundOutputKey,
    ReverseThresholdSummaryKey,
    RootMatchResult,
    SourceRootMatchKey,
    SpatialInterfaceKey,
)
from number_compiler.hashlife.tiles.tile_result_types import is_execution_key
from number_compiler.hashlife.tiles.tile_result_validation import (
    validate_boundary_operands,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileID, TileLease
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.tile_alphabet_contract import (
    CANONICAL_TILE_ALPHABET_VERSION,
)
from number_compiler.resources.tile_reverse_output_inventory import (
    reverse_bound_output_scalar_slots,
    valid_reverse_bound_output,
)


def audit_tile_results(
    arena: CompletedResultArena,
    containers: Mapping[int, object],
) -> tuple[set[int], set[tuple[int, int]]]:
    """Check memo values and the complete bidirectional retirement index."""
    state = arena.audit_snapshot()
    tile_state = state.tiles
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    inventory = {item.owner: item for item in arena.ledger.inventory()}
    memo_inventory = inventory.get(state.memo_owner)
    reverse_inventory = inventory.get(state.reverse_owner)
    tile_lease_inventory = inventory.get(tile_state.lease_owner)
    operand_records = state.operand_records
    operand_inventory = inventory.get(state.operand_owner)
    pending_records = state.pending_records
    pending_inventory = inventory.get(state.pending_owner)
    pending_slots = sum(
        type(record) is int and record == 1 for record in pending_records
    )
    observed_memo_nodes = sum(
        result.retained_nodes
        if type(result) is CompletedInterfaceResult
        else reverse_bound_output_scalar_slots(result)
        if type(result) is ReverseBoundOutput
        else 0
        for result in state.memo.values()
    )
    stores_valid = (
        id(containers.get(state.memo_owner)) == state.memo_store_identity
        and id(containers.get(state.reverse_owner)) == state.reverse_store_identity
        and id(containers.get(state.variant_owner)) == state.variant_store_identity
        and id(containers.get(state.operand_owner)) == state.operand_store_identity
        and id(containers.get(state.pending_owner)) == state.pending_store_identity
        and state.pending_ledger is arena.ledger
        and state.pending_tiles is arena.tiles
        and state.pending_acquisition_owner == state.pending_owner
        and state.pending_acquisitions_store_identity == state.pending_store_identity
        and arena.tiles.ledger is arena.ledger
        and arena.interfaces.ledger is arena.ledger
        and tile_state.results is arena
        and any(root is arena for root in arena.ledger.iter_execution_roots())
        and any(
            root is arena.action_authority
            for root in arena.ledger.iter_execution_roots()
        )
        and getattr(state.validate_action, "__self__", None) is state.action_authority
        and getattr(state.signature_for, "__self__", None) is state.action_authority
        and (
            state.validated_signature_for is None
            or getattr(state.validated_signature_for, "__self__", None)
            is state.action_authority
        )
        and (
            state.validate_input is None
            or getattr(state.validate_input, "__self__", None) is state.action_authority
        )
        and (
            state.validate_output is None
            or getattr(state.validate_output, "__self__", None)
            is state.action_authority
        )
        and (
            state.validate_fused_action is None
            or getattr(state.validate_fused_action, "__self__", None)
            is state.action_authority
        )
        and (
            state.validate_fused_wiring is None
            or getattr(state.validate_fused_wiring, "__self__", None)
            is state.action_authority
        )
        and memo_inventory is not None
        and memo_inventory.entries == len(state.memo)
        and memo_inventory.observed_entries == len(state.memo)
        and memo_inventory.nodes == observed_memo_nodes
        and memo_inventory.observed_nodes == observed_memo_nodes
        and reverse_inventory is not None
        and reverse_inventory.entries == len(state.reverse)
        and reverse_inventory.observed_entries == len(state.reverse)
        and operand_inventory is not None
        and operand_inventory.entries
        == len(operand_records) + state.operand_pending_release_entries
        and operand_inventory.observed_entries == len(operand_records)
        and type(state.operand_pending_release_entries) is int
        and state.operand_pending_release_entries >= 0
        and pending_inventory is not None
        and tile_lease_inventory is not None
        and pending_inventory.entries
        == len(pending_records) + state.pending_clear_entries
        and pending_inventory.observed_entries == len(pending_records)
        and pending_inventory.nodes == len(pending_records) + state.pending_clear_nodes
        and type(state.pending_clear_entries) is int
        and type(state.pending_clear_nodes) is int
        and state.pending_clear_entries >= 0
        and state.pending_clear_nodes >= 0
        and type(state.pending_tile_reservations) is int
        and state.pending_tile_reservations >= 0
        and tile_lease_inventory.entries
        == len(tile_state.leases) + pending_slots + state.pending_tile_reservations
        and tile_lease_inventory.observed_entries == len(tile_state.leases)
        and type(state.boundary_lease_count) is int
        and 0 <= state.boundary_lease_count <= len(tile_state.leases)
        and arena.ledger.counters.get(_shared_keys.BOUNDARY_TILE_LEASE_PEAK, 0)
        >= state.boundary_lease_count
    )
    expected: dict[
        TileID,
        set[
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
        ],
    ] = {}
    expected_variants: dict[ResultVariantKey | FusedVariantKey, int] = {}

    live_tiles = set(tile_state.leases.values())
    for view, count in operand_records.items():
        valid_operand = (
            type(view) is BoundaryTileView and type(count) is int and count > 0
        )
        try:
            if type(view) is not BoundaryTileView:
                raise TypeError("leased boundary operand has another sort")
            view.__post_init__()
            record = arena.tiles.resolve(view.tile)
            valid_operand &= (
                view.tile in live_tiles
                and view.source_offset <= record.width
                and view.source_offset + view.relative_extent <= record.width
            )
        except (TypeError, ValueError, KeyError, AttributeError):
            valid_operand = False
        if valid_operand:
            approved.add(id(view))
        else:
            invalid.add((state.operand_owner, id(view)))

    for acquisition in pending_records:
        if acquisition is None:
            continue
        if type(acquisition) is int and acquisition == 1:
            approved.add(id(acquisition))
            continue
        if type(acquisition) is TileLease:
            lease_state = acquisition.audit_snapshot()
            try:
                tile = tile_state.leases[lease_state.identity]
                valid_pending_lease = (
                    lease_state.arena is arena.tiles
                    and lease_state.closed is False
                    and type(tile) is TileID
                    and tile.owner is arena.tiles.owner
                    and tile.local_id in tile_state.nodes
                )
            except (KeyError, TypeError, AttributeError):
                valid_pending_lease = False
            if valid_pending_lease:
                approved.add(id(acquisition))
            else:
                invalid.add((state.pending_owner, id(acquisition)))
            continue
        invalid.add((state.pending_owner, id(acquisition)))

    def admissible_value(
        signature: PortSignatureID, assignment: dict[PortVariable, int]
    ) -> bool:
        declaration = arena.interfaces.interface(signature)
        functions = arena.interfaces.functions
        node = functions.resolve(declaration.admissible)
        while node.variable is not None:
            variable = node.variable
            base = PortVariable(variable.time, variable.side, variable.role, 0)
            node = functions.nodes[
                node.high if (assignment[base] >> variable.bit) & 1 else node.low
            ]
        terminal = node.terminal
        return terminal is not None and terminal.kind == "atom" and terminal.value == 1

    def valid_ports(signature: object, values: object) -> bool:
        if type(signature) is not PortSignatureID:
            return False
        if not is_exact_integer_tuple(values):
            return False
        try:
            declaration = arena.interfaces.interface(signature)
            if len(values) != len(declaration.inputs):
                return False
            assignment: dict[PortVariable, int] = {}
            for port, value in zip(declaration.inputs, values, strict=True):
                if not 0 <= value < port.cardinality:
                    return False
                assignment[port.variable] = value
            return admissible_value(signature, assignment)
        except (TypeError, ValueError, KeyError, AttributeError):
            return False

    def valid_boundaries(
        value: object,
        expected: TileID,
        child: FieldCellActionID | None = None,
        *,
        output: bool = False,
    ) -> bool:
        if type(value) is not BoundaryTileOperands:
            return False
        try:
            alphabet = arena.tiles.resolve(expected).alphabet
        except (TypeError, ValueError, KeyError, AttributeError):
            return False
        for view in (value.left, value.right):
            if view is None:
                continue
            if type(view) is not BoundaryTileView:
                return False
            try:
                view.__post_init__()
                record = arena.tiles.resolve(view.tile)
                if (
                    view.source_offset > record.width
                    or view.source_offset + view.relative_extent > record.width
                ):
                    return False
                domain = state.validate_output if output else state.validate_input
                if child is not None and domain is not None:
                    domain(child, view.tile)
                elif record.alphabet != alphabet:
                    return False
            except (TypeError, ValueError, KeyError, AttributeError):
                return False
        return True

    def valid_bound_ports(
        value: object,
        expected: TileID,
        child: FieldCellActionID | None = None,
        *,
        output: bool = False,
    ) -> bool:
        if type(value) is not BoundPorts:
            return False
        try:
            value.__post_init__()
            declaration = arena.interfaces.interface(value.signature)
            return (
                value.wiring.orientation in declaration.orientations
                and 0 <= value.wiring.phase < declaration.phase_count
                and valid_ports(value.signature, value.ports)
                and valid_boundaries(value.boundaries, expected, child, output=output)
            )
        except (TypeError, ValueError, KeyError, AttributeError):
            return False

    def valid_fusion(
        value: object,
        consumer: BoundPorts,
        expected: TileID,
        action: FieldCellActionID,
        *,
        output: bool = False,
    ) -> bool:
        if type(value) is not FusedBoundaryContract:
            return False
        try:
            value.__post_init__()
            children_hook = getattr(arena.action_authority, "action_children", None)
            before_action: FieldCellActionID | None = None
            after_action: FieldCellActionID | None = None
            if children_hook is not None:
                if (
                    getattr(children_hook, "__self__", None)
                    is not arena.action_authority
                ):
                    return False
                children = children_hook(action)
                if not is_exact_object_tuple(children) or len(children) != 2:
                    return False
                before, after = children
                if (
                    type(before) is not FieldCellActionID
                    or type(after) is not FieldCellActionID
                ):
                    return False
                before_action = before
                after_action = after
                state.validate_action(before_action)
                state.validate_action(after_action)
                if (
                    state.signature_for(before_action) != value.producer.signature
                    or state.signature_for(after_action) != value.consumer.signature
                ):
                    return False
            valid = (
                value.consumer == consumer
                and valid_bound_ports(
                    value.producer, expected, before_action, output=output
                )
                and valid_bound_ports(
                    value.consumer, expected, after_action, output=output
                )
                and state.validate_fused_action is not None
            )
            if not valid or state.validate_fused_action is None:
                return False
            state.validate_fused_action(action)
            if state.validate_fused_wiring is None:
                return value.producer.wiring == value.consumer.wiring
            state.validate_fused_wiring(
                action,
                value.producer.wiring,
                value.consumer.wiring,
            )
            return True
        except (TypeError, ValueError, KeyError, AttributeError):
            return False

    for key, result in state.memo.items():
        valid = stores_valid and type(key) in (
            PoweredResultKey,
            PoweredInterfaceKey,
            FusedInterfaceKey,
            CausalInterfaceKey,
            DirectedTransferKey,
            ReverseThresholdSummaryKey,
            ReverseBoundOutputKey,
            SourceRootMatchKey,
            BehaviorBindingKey,
            NormalizedRegionKey,
            BoundaryConcatKey,
            SpatialInterfaceKey,
        )
        execution_key = cast(
            PoweredResultKey
            | PoweredInterfaceKey
            | FusedInterfaceKey
            | CausalInterfaceKey
            | DirectedTransferKey
            | BehaviorBindingKey,
            key,
        )
        try:
            if type(key) is SpatialInterfaceKey:
                spatial_key = key
                if type(result) is not LocalInterfaceID:
                    raise TypeError("spatial composition has another value sort")
                valid &= (
                    type(spatial_key.left) is LocalInterfaceID
                    and type(spatial_key.right) is LocalInterfaceID
                    and type(spatial_key.wiring) is ResultWiring
                )
                spatial_key.wiring.__post_init__()
                signature = arena.interfaces.interface(spatial_key.wiring.signature)
                valid &= (
                    spatial_key.wiring.orientation in signature.orientations
                    and 0 <= spatial_key.wiring.phase < signature.phase_count
                    and arena.interfaces.resolve(spatial_key.left).signature
                    == spatial_key.wiring.signature
                    and arena.interfaces.resolve(spatial_key.right).signature
                    == spatial_key.wiring.signature
                    and arena.interfaces.resolve(result).signature
                    == spatial_key.wiring.signature
                )
                if valid:
                    approved.update((id(spatial_key), id(result)))
                else:
                    invalid.add((state.memo_owner, id(spatial_key)))
                continue
            if type(key) is NormalizedRegionKey:
                if type(result) is not NormalizedRegionResult:
                    raise TypeError("normalized region has another value sort")
                validate_normalized_region_value(arena, key, result, published=True)
                approved.update((id(key), id(result)))
                for tile in dict.fromkeys((key.input, result.view.tile)):
                    expected.setdefault(tile, set()).add(key)
                continue
            if type(key) is BoundaryConcatKey:
                if type(result) is not BoundaryConcatResult:
                    raise TypeError("boundary concat has another value sort")
                validate_boundary_concat_value(arena, key, result, published=True)
                approved.update((id(key), id(result)))
                for tile in dict.fromkeys(
                    (key.first.tile, key.second.tile, result.view.tile)
                ):
                    expected.setdefault(tile, set()).add(key)
                continue
            if type(key) is ReverseThresholdSummaryKey:
                key.__post_init__()
                node = arena.tiles.resolve(key.input)
                alphabet = arena.tiles.alphabet(node.alphabet)
                if type(result) is not BlockSummary:
                    raise TypeError("reverse threshold summary has another value sort")
                result.__post_init__()
                valid &= (
                    alphabet.radix == key.base
                    and alphabet.blank == 2 * key.base - 1
                    and alphabet.symbol_count == 2 * key.base
                    and alphabet.interpretation
                    == "unsigned-radix-cell-with-explicit-blank"
                    and alphabet.version == CANONICAL_TILE_ALPHABET_VERSION
                    and result.length == node.extent
                )
                if valid:
                    approved.update((id(key), id(result)))
                    expected.setdefault(key.input, set()).add(key)
                else:
                    invalid.add((state.memo_owner, id(key)))
                continue
            if type(key) is ReverseBoundOutputKey:
                valid &= valid_reverse_bound_output(arena, key, result)
                if valid:
                    approved.update((id(key), id(result)))
                    expected.setdefault(key.input, set()).add(key)
                else:
                    invalid.add((state.memo_owner, id(key)))
                continue
            if type(key) is SourceRootMatchKey:
                if type(result) is not RootMatchResult:
                    raise TypeError("source root match has another value sort")
                validate_source_root_match_value(arena, key, result, published=True)
                approved.update((id(key), id(result)))
                expected.setdefault(key.input, set()).add(key)
                continue
            valid &= (
                type(execution_key.action) is FieldCellActionID
                and type(execution_key.input) is TileID
                and type(execution_key.wiring) is ResultWiring
                and (
                    type(execution_key) is DirectedTransferKey
                    or (
                        type(execution_key) is PoweredResultKey
                        and execution_key.fusion is not None
                    )
                    or valid_boundaries(execution_key.boundaries, execution_key.input)
                )
            )
            authority_owner = getattr(arena.action_authority, "owner", None)
            authority_kind = getattr(
                arena.action_authority,
                "action_kind",
                "field-cell-action",
            )
            if type(authority_owner) is not ArenaToken:
                raise ValueError("result action authority has no scoped owner")
            execution_key.action.validate(authority_owner, authority_kind)
            state.validate_action(execution_key.action)
            valid &= (
                state.signature_for(execution_key.action)
                == execution_key.wiring.signature
            )
            arena.tiles.resolve(execution_key.input)
            if state.validate_input is not None:
                state.validate_input(execution_key.action, execution_key.input)
            if type(execution_key) is FusedInterfaceKey:
                if state.validate_fused_action is None:
                    raise ValueError("fused result has no action admission authority")
                state.validate_fused_action(execution_key.action)
                children_hook = getattr(arena.action_authority, "action_children", None)
                before, after = execution_key.before, execution_key.after
                if children_hook is None:
                    valid &= before is None and after is None
                else:
                    if (
                        type(before) is not FieldCellActionID
                        or type(after) is not FieldCellActionID
                    ):
                        raise TypeError("fused memo lost its explicit temporal edge")
                    before.validate(authority_owner, authority_kind)
                    after.validate(authority_owner, authority_kind)
                    state.validate_action(before)
                    state.validate_action(after)
                    valid &= (
                        getattr(children_hook, "__self__", None)
                        is arena.action_authority
                        and children_hook(execution_key.action) == (before, after)
                        and state.signature_for(before)
                        == execution_key.producer_context.signature
                        and state.signature_for(after) == execution_key.wiring.signature
                    )
                validate_boundary_operands(
                    arena.tiles, execution_key.consumer_boundaries
                )
                for tile in execution_key.consumer_boundaries.tile_ids():
                    if after is not None and state.validate_input is not None:
                        state.validate_input(after, tile)
                    else:
                        valid &= valid_boundaries(
                            execution_key.consumer_boundaries, execution_key.input
                        )
            execution_key.wiring.__post_init__()
            signature = arena.interfaces.interface(execution_key.wiring.signature)
            valid &= 0 <= execution_key.wiring.phase < signature.phase_count
            valid &= execution_key.wiring.orientation in signature.orientations
            if type(execution_key) is CausalInterfaceKey:
                causal_key = execution_key
                valid &= valid_ports(
                    causal_key.wiring.signature,
                    causal_key.ports,
                )
                if causal_key.fusion is not None:
                    valid &= valid_fusion(
                        causal_key.fusion,
                        BoundPorts(
                            causal_key.ports,
                            causal_key.wiring,
                            causal_key.boundaries,
                        ),
                        causal_key.input,
                        causal_key.action,
                    )
            elif type(execution_key) is BehaviorBindingKey:
                behavior_key = execution_key
                valid &= type(behavior_key.request) is PoweredResultKey
                valid &= valid_ports(
                    behavior_key.wiring.signature,
                    behavior_key.ports,
                )
                region = behavior_key.region
                if region is not None:
                    if (
                        type(region) is not tuple
                        or len(region) != 2
                        or any(type(n) is not int for n in region)
                    ):
                        raise TypeError("behavior region has another geometry sort")
                    valid &= _proper_dyadic_region(
                        region, arena.tiles.resolve(behavior_key.input).level
                    )
                arena.interfaces.resolve_future_profile(behavior_key.profile)
                if behavior_key.fusion is not None:
                    valid &= valid_fusion(
                        behavior_key.fusion,
                        behavior_key.request.bound_ports,
                        behavior_key.input,
                        behavior_key.action,
                    )
            elif type(execution_key) is PoweredResultKey:
                powered_key = execution_key
                region = powered_key.region
                if region is not None:
                    if (
                        type(region) is not tuple
                        or len(region) != 2
                        or any(type(n) is not int for n in region)
                    ):
                        raise TypeError("causal region has another geometry sort")
                    valid &= _proper_dyadic_region(
                        region, arena.tiles.resolve(powered_key.input).level
                    )
                valid &= valid_ports(powered_key.wiring.signature, powered_key.ports)
                if powered_key.fusion is not None:
                    valid &= valid_ports(
                        powered_key.wiring.signature,
                        powered_key.ports,
                    )
                    valid &= valid_fusion(
                        powered_key.fusion,
                        powered_key.bound_ports,
                        powered_key.input,
                        powered_key.action,
                    )
            elif type(execution_key) is FusedInterfaceKey:
                producer_wiring = execution_key.producer_wiring
                if type(producer_wiring) is not ResultWiring:
                    raise TypeError("fused producer has another wiring sort")
                producer_wiring.__post_init__()
                producer_signature = arena.interfaces.interface(
                    producer_wiring.signature
                )
                valid &= (
                    producer_wiring.orientation in producer_signature.orientations
                    and 0 <= producer_wiring.phase < producer_signature.phase_count
                    and valid_ports(producer_wiring.signature, execution_key.ports)
                )
                if state.validate_fused_wiring is None:
                    valid &= producer_wiring == execution_key.wiring
                else:
                    state.validate_fused_wiring(
                        execution_key.action,
                        producer_wiring,
                        execution_key.wiring,
                    )
            elif type(execution_key) is DirectedTransferKey:
                directed = execution_key
                children_hook = getattr(arena.action_authority, "action_children", None)
                initial_hook = getattr(arena.action_authority, "initial_ports", None)
                if (
                    not callable(children_hook)
                    or not callable(initial_hook)
                    or getattr(children_hook, "__self__", None)
                    is not arena.action_authority
                    or getattr(initial_hook, "__self__", None)
                    is not arena.action_authority
                    or children_hook(directed.action) is not None
                    or type(directed.side) is not int
                    or directed.side not in (0, 1)
                    or type(directed.incoming_state) is not int
                ):
                    raise ValueError(
                        "directed transfer has a malformed primitive context"
                    )
                initial = initial_hook(directed.action)
                if not is_exact_integer_tuple(initial) or len(initial) != 2:
                    raise ValueError("directed transfer has malformed initial ports")
                directed_ports = (
                    (directed.incoming_state, initial[1])
                    if directed.side == 0
                    else (initial[0], directed.incoming_state)
                )
                valid &= valid_ports(directed.wiring.signature, directed_ports)
            if type(execution_key) is PoweredResultKey:
                valid &= type(result) is CompletedResult
                if type(result) is not CompletedResult:
                    raise TypeError("completed result has another value sort")
                result.__post_init__()
                output = arena.tiles.resolve(result.output)
                valid &= (
                    execution_key.region is None
                    or output.level == execution_key.region[1]
                )
                if state.validate_output is not None:
                    state.validate_output(execution_key.action, result.output)
                outgoing = arena.interfaces.resolve(result.outgoing)
                valid &= (
                    outgoing.signature == execution_key.wiring.signature
                    and result.relative_extent == output.extent
                    and result.relative_extent <= output.width
                    and valid_ports(outgoing.signature, result.outgoing_ports)
                    and (
                        result.observed_input_ports is None
                        or valid_ports(
                            execution_key.wiring.signature,
                            result.observed_input_ports,
                        )
                    )
                    and valid_boundaries(result.outgoing_boundaries, result.output)
                )
                result_consumer = BoundPorts(
                    result.outgoing_ports,
                    execution_key.wiring,
                    result.outgoing_boundaries,
                )
                if execution_key.fusion is None:
                    valid &= result.fusion is None
                else:
                    valid &= valid_fusion(
                        result.fusion,
                        result_consumer,
                        result.output,
                        execution_key.action,
                        output=True,
                    )
            elif type(execution_key) is CausalInterfaceKey:
                if type(result) is not CompletedInterfaceResult:
                    raise TypeError("causal interface has another value sort")
                validate_published_causal_interface_value(arena, execution_key, result)
                result.__post_init__()
                valid &= (
                    result.level == arena.tiles.resolve(execution_key.input).level
                    and arena.interfaces.resolve(result.interface).signature
                    == execution_key.wiring.signature
                    and valid_ports(
                        execution_key.wiring.signature,
                        result.observed_input_ports,
                    )
                    and valid_ports(
                        execution_key.wiring.signature,
                        result.outgoing_ports,
                    )
                )
            elif type(execution_key) is DirectedTransferKey:
                if type(result) is not int:
                    raise TypeError("directed transfer has another value sort")
                declaration = arena.interfaces.interface(execution_key.wiring.signature)
                valid &= (
                    len(declaration.inputs) == 2
                    and 0 <= result < declaration.inputs[execution_key.side].cardinality
                )
            elif type(execution_key) is BehaviorBindingKey:
                if type(result) is not CompletedBehaviorClassification:
                    raise TypeError("behavior binding has another value sort")
                validate_published_behavior(arena, execution_key, result)
            else:
                if type(result) is not LocalInterfaceID:
                    raise TypeError("powered interface has another value sort")
                valid &= (
                    arena.interfaces.resolve(result).signature
                    == execution_key.wiring.signature
                )
        except (TypeError, ValueError, KeyError, AttributeError):
            valid = False
        if valid:
            approved.update((id(execution_key), id(result)))
            tile_values = [execution_key.input]
            if type(execution_key) is not DirectedTransferKey:
                tile_values.extend(execution_key.boundaries.tile_ids())
            if type(execution_key) is FusedInterfaceKey:
                tile_values.extend(execution_key.consumer_boundaries.tile_ids())
            if (
                type(execution_key) is PoweredResultKey
                and execution_key.fusion is not None
            ):
                tile_values.extend(execution_key.fusion.producer.boundaries.tile_ids())
                tile_values.extend(execution_key.fusion.consumer.boundaries.tile_ids())
            if (
                type(execution_key) is CausalInterfaceKey
                and execution_key.fusion is not None
            ):
                tile_values.extend(execution_key.fusion.producer.boundaries.tile_ids())
                tile_values.extend(execution_key.fusion.consumer.boundaries.tile_ids())
            if (
                type(execution_key) is BehaviorBindingKey
                and execution_key.fusion is not None
            ):
                tile_values.extend(execution_key.fusion.producer.boundaries.tile_ids())
                tile_values.extend(execution_key.fusion.consumer.boundaries.tile_ids())
            if type(result) is CompletedResult:
                tile_values.extend(
                    (result.output, *result.outgoing_boundaries.tile_ids())
                )
                if result.fusion is not None:
                    tile_values.extend(result.fusion.producer.boundaries.tile_ids())
                    tile_values.extend(result.fusion.consumer.boundaries.tile_ids())
            tiles = tuple(dict.fromkeys(tile_values))
            for tile in tiles:
                expected.setdefault(tile, set()).add(execution_key)
            if type(execution_key) is PoweredResultKey:
                result_variant = ResultVariantKey(
                    execution_key.action,
                    execution_key.input,
                    execution_key.wiring,
                    execution_key.boundaries,
                    None
                    if execution_key.fusion is None
                    else execution_key.fusion.producer,
                    execution_key.region,
                )
                expected_variants[result_variant] = (
                    expected_variants.get(result_variant, 0) + 1
                )
            elif type(execution_key) is FusedInterfaceKey:
                producer_wiring = execution_key.producer_wiring
                if type(producer_wiring) is not ResultWiring:
                    raise TypeError("fused producer has another wiring sort")
                fused_variant = FusedVariantKey(
                    execution_key.action,
                    execution_key.input,
                    execution_key.wiring,
                    producer_wiring,
                    execution_key.boundaries,
                    execution_key.before,
                    execution_key.after,
                    execution_key.consumer_boundaries,
                )
                expected_variants[fused_variant] = (
                    expected_variants.get(fused_variant, 0) + 1
                )
        else:
            invalid.add((state.memo_owner, id(key)))

    observed: dict[
        TileID,
        set[
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
        ],
    ] = {}
    visited_members: set[ResultDependencyMember] = set()
    for tile, keys in expected.items():
        current = state.reverse.get(ResultDependencyHead(tile))
        previous = None
        while is_execution_key(current):
            member_key = ResultDependencyMember(tile, current)
            if member_key in visited_members:
                invalid.add((state.reverse_owner, id(member_key)))
                break
            links = state.reverse.get(member_key)
            if type(links) is not ResultDependencyLinks or links.previous != previous:
                invalid.add((state.reverse_owner, id(member_key)))
                break
            visited_members.add(member_key)
            observed.setdefault(tile, set()).add(current)
            previous, current = current, links.following
        if current is not None:
            invalid.add((state.reverse_owner, id(tile)))
        if observed.get(tile, set()) != keys:
            invalid.add((state.reverse_owner, id(tile)))
    for reverse_key, reverse_value in state.reverse.items():
        valid = False
        if type(reverse_key) is ResultDependencyHead:
            valid = (
                reverse_key.tile in expected
                and type(reverse_value)
                in (
                    PoweredResultKey,
                    PoweredInterfaceKey,
                    FusedInterfaceKey,
                    CausalInterfaceKey,
                    DirectedTransferKey,
                    ReverseThresholdSummaryKey,
                    ReverseBoundOutputKey,
                    SourceRootMatchKey,
                    BehaviorBindingKey,
                    NormalizedRegionKey,
                    BoundaryConcatKey,
                )
                and reverse_value in expected[reverse_key.tile]
            )
        elif type(reverse_key) is ResultDependencyMember:
            valid = (
                reverse_key in visited_members
                and type(reverse_value) is ResultDependencyLinks
            )
        if valid:
            approved.update((id(reverse_key), id(reverse_value)))
        else:
            invalid.add((state.reverse_owner, id(reverse_key)))
    if set(observed) != set(expected):
        invalid.add((state.reverse_owner, state.reverse_store_identity))
    for stored_variant, count in state.variants.items():
        if (
            type(stored_variant) in (ResultVariantKey, FusedVariantKey)
            and type(count) is int
            and count > 0
            and expected_variants.get(stored_variant) == count
        ):
            approved.add(id(stored_variant))
        else:
            invalid.add((state.variant_owner, id(stored_variant)))
    if dict(state.variants) != expected_variants:
        invalid.add((state.variant_owner, state.variant_store_identity))
    if not invalid:
        approved.update(
            (
                id(arena),
                state.memo_store_identity,
                state.reverse_store_identity,
                state.variant_store_identity,
                state.operand_store_identity,
            )
        )
    return approved, invalid


__all__ = ["audit_tile_results"]


def _proper_dyadic_region(region: tuple[int, int], source_level: int) -> bool:
    """Check a non-root dyadic region after exact-integer admission."""
    origin, level = region
    return (
        origin >= 0
        and 0 <= level <= source_level
        and origin % (1 << level) == 0
        and origin + (1 << level) <= (1 << source_level)
        and region != (0, source_level)
    )
