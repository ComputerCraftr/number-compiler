"""Independent ownership audit for the canonical tile execution runtime."""

from __future__ import annotations

from collections.abc import Mapping
from typing import cast

import number_compiler.resources.tile_causal_workspace_inventory as causal_inventory
import number_compiler.resources.tile_scheduler_inventory_support as scheduler_support
from number_compiler.arithmetic.contracts.block_effect import _effect_key
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.formula.summary import BlockSummary
from number_compiler.arithmetic.functions.finite_function_types import AtomSort
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    ReverseFrobeniusPlan,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.tile_action_algebra import (
    ActionSemanticKey,
    blank_context_metadata,
)
from number_compiler.hashlife.actions.tile_action_algebra import (
    PrimitiveTileAction as _Action,
)
from number_compiler.hashlife.execution.tile_application import TileApplication
from number_compiler.hashlife.execution.tile_fused_kernel import LeafProductKey
from number_compiler.hashlife.execution.tile_kernel import (
    PrimitiveTileKernelAdapter,
)
from number_compiler.hashlife.execution.tile_kernel_contract import (
    TILE_KERNEL_CONTRACT,
)
from number_compiler.hashlife.execution.tile_scheduler import (
    TileScheduler,
)
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
from number_compiler.hashlife.interfaces.tile_interface_compilation import (
    input_ports_for_kernel,
    output_sorts_for_kernel,
)
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
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
    NormalizedRegionKey,
    NormalizedRegionResult,
    PoweredInterfaceKey,
    PoweredResultKey,
    ReverseBoundOutputKey,
    ReverseThresholdSummaryKey,
    RootMatchResult,
    SourceRootMatchKey,
    SpatialInterfaceKey,
)
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.tiles.tiles import (
    TileAlphabet,
    TileArena,
    TileID,
    TileLease,
)
from number_compiler.resources.causal_workspace import (
    CausalSpatialWorkspace,
    CausalTaskWorkspace,
)
from number_compiler.resources.fused_traversal_inventory import (
    audit_fused_traversal_workspace,
)
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit
from number_compiler.resources.reverse_morphism_inventory import audit_reverse_morphisms
from number_compiler.resources.reverse_residual_inventory import audit_reverse_residuals
from number_compiler.resources.tile_alphabet_contract import (
    CANONICAL_TILE_ALPHABET_VERSION,
)
from number_compiler.resources.tile_reverse_output_inventory import (
    valid_reverse_bound_output,
)
from number_compiler.resources.tile_runtime_validation import (
    valid_boundaries,
    valid_causal_interface_record,
    valid_ports,
    valid_request,
    valid_source_root_match_record,
)


def _has_distinct_identity(left: object, right: object) -> bool:
    """Preserve exact store-separation checks across unrelated generic types."""
    return left is not right


def _matches_alphabet(
    adapter: PrimitiveTileKernelAdapter, expected: TileAlphabet, tile: TileID
) -> bool:
    record = adapter.tiles.resolve(tile)
    return adapter.tiles.alphabet(record.alphabet) == expected


def audit_tile_runtime(
    ledger: object,
    containers: Mapping[int, object],
    roots: tuple[object, ...],
    contracts: PayloadAuditContractAudit | None = None,
) -> tuple[set[int], set[tuple[int, int]]]:
    """Validate action records and every retained application result pin."""
    approved, invalid = audit_reverse_morphisms(ledger, roots, contracts)
    invalid.update(audit_reverse_residuals(ledger, roots, contracts))
    adapters = tuple(root for root in roots if type(root) is PrimitiveTileKernelAdapter)
    schedulers = tuple(root for root in roots if type(root) is TileScheduler)
    physical_schedulers = tuple(
        scheduler for scheduler in schedulers if not scheduler.is_source_only
    )
    applications = tuple(root for root in roots if type(root) is TileApplication)

    for adapter in adapters:
        state = adapter.audit_snapshot()
        adapter_scheduler = next(
            (
                scheduler
                for scheduler in physical_schedulers
                if scheduler.adapter is adapter and scheduler.results is adapter.results
            ),
            None,
        )
        stores = (
            (state.action_owner, state.action_store_identity),
            (state.action_key_owner, state.action_key_store_identity),
            (state.leaf_owner, state.leaf_store_identity),
            (state.compose_owner, state.compose_store_identity),
        )
        valid_root = (
            adapter.ledger is ledger
            and adapter.tiles.ledger is ledger
            and adapter.kernels.ledger is ledger
            and adapter.quotients.ledger is ledger
            and state.ledger is ledger
            and state.owner is adapter.owner
            and all(id(containers.get(owner)) == store_id for owner, store_id in stores)
            and type(state.next_action) is int
            and state.next_action >= 0
        )
        fused_approved, fused_invalid = audit_fused_traversal_workspace(
            adapter,
            containers,
            state.fused_workspace,
        )
        approved.update(fused_approved)
        invalid.update(fused_invalid)
        valid_root &= not fused_invalid
        signatures: dict[PortSignatureID, set[int]] = {}
        expected_keys: dict[int, ActionSemanticKey] = {}
        for index, record in state.actions.items():
            valid = valid_root and type(index) is int and type(record) is _Action
            try:
                if not 0 <= index < state.next_action:
                    raise ValueError("action index lies outside its arena")
                action = FieldCellActionID(
                    adapter.owner,
                    "field-cell-action",
                    index,
                )
                adapter.validate_action(action)
                kernel = adapter.kernels.kernel(record.kernel)
                declaration = adapter.quotients.interface(record.signature)
                behavior = (TILE_KERNEL_CONTRACT, _effect_key(kernel.effect))
                declaration.kernel.validate()
                valid &= (
                    declaration.kernel.behavior == behavior
                    and declaration.inputs == input_ports_for_kernel(kernel)
                    and declaration.outputs == output_sorts_for_kernel(kernel)
                    and declaration.phase_count == 1
                    and declaration.orientations == (0,)
                )
                expected_frobenius = (
                    ReverseFrobeniusPlan.for_steps(
                        maximum_classes=8,
                        bits=5,
                        steps=record.repetitions,
                        growth_certificate=DECIMAL_REVERSE_GROWTH_CERTIFICATE,
                    )
                    if record.homogeneous
                    and type(kernel.effect) is BaseBlockEffect
                    and kernel.effect.base == 10
                    else None
                )
                valid &= (
                    type(record.reverse_frobenius) is type(expected_frobenius)
                    and record.reverse_frobenius == expected_frobenius
                    and (
                        record.reverse_frobenius is None
                        or record.reverse_frobenius.growth_certificate
                        is DECIMAL_REVERSE_GROWTH_CERTIFICATE
                    )
                )
                if record.children is None:
                    expected_key: ActionSemanticKey = (
                        "power",
                        record.kernel,
                        1,
                        record.cocycle,
                    )
                    valid &= (
                        record.repetitions == 1
                        and type(record.cocycle) is TemporalCocycle
                        and type(record.spatial_events_add) is bool
                        and record.spatial_events_add
                        == (
                            adapter.family_hooks is not None
                            and adapter.family_hooks.owns_effect(kernel.effect)
                            and adapter.family_hooks.spatial_events_add
                        )
                        and blank_context_metadata(record)
                        == (
                            kernel.effect.blank_left_tail,
                            kernel.effect.blank_right_tail,
                            kernel.effect.stable_blank_output,
                        )
                    )
                else:
                    before, after = record.children
                    valid &= (
                        type(before) is FieldCellActionID
                        and type(after) is FieldCellActionID
                        and before.owner is adapter.owner
                        and after.owner is adapter.owner
                        and before.kind == "field-cell-action"
                        and after.kind == "field-cell-action"
                        and type(before.local_id) is int
                        and type(after.local_id) is int
                        and 0 <= before.local_id < index
                        and 0 <= after.local_id < index
                        and record.repetitions >= 2
                    )
                    first = state.actions[before.local_id]
                    second = state.actions[after.local_id]
                    homogeneous = (
                        first.kernel == second.kernel
                        and first.signature == second.signature
                        and expected_keys.get(before.local_id, (None,))[0] == "power"
                        and expected_keys.get(after.local_id, (None,))[0] == "power"
                    )
                    expected_key = (
                        (
                            "power",
                            record.kernel,
                            record.repetitions,
                            record.cocycle,
                        )
                        if homogeneous
                        else ("compose", before, after)
                    )
                    valid &= (
                        second.kernel == record.kernel
                        and type(record.spatial_events_add) is bool
                        and record.spatial_events_add
                        == (first.spatial_events_add or second.spatial_events_add)
                        and second.signature == record.signature
                        and (
                            homogeneous
                            or (
                                adapter.kernels.kernel(first.kernel).base == kernel.base
                                and adapter.kernels.kernel(first.kernel).blank
                                == kernel.blank
                            )
                        )
                        and record.repetitions == first.repetitions + second.repetitions
                        and record.cocycle
                        == TemporalCocycle(
                            first.cocycle.physical_ticks
                            + second.cocycle.physical_ticks,
                            first.cocycle.event_weight + second.cocycle.event_weight,
                            first.cocycle.frame_shift + second.cocycle.frame_shift,
                        )
                        and blank_context_metadata(record)
                        == blank_context_metadata(first, second)
                    )
                mapped = state.action_keys.get(expected_key)
                valid &= type(mapped) is int and mapped == index
                admissible = adapter.quotients.functions.resolve(
                    declaration.admissible,
                )
                admissible_output = admissible.signature.output
                valid &= (
                    admissible.signature.inputs == declaration.inputs
                    and type(admissible_output) is AtomSort
                    and admissible_output.name == "boolean"
                    and admissible_output.cardinality == 2
                )
                if valid:
                    expected_keys[index] = expected_key
                    signatures.setdefault(record.signature, set()).add(kernel.blank)
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.add(id(record))
                if record.reverse_frobenius is not None:
                    approved.add(id(record.reverse_frobenius))
                    if record.reverse_frobenius.growth_certificate is not None:
                        approved.add(id(record.reverse_frobenius.growth_certificate))
                    approved.update(
                        id(sector) for sector in record.reverse_frobenius.sectors
                    )
            else:
                invalid.add((state.action_owner, id(record)))
        for semantic_key, index in state.action_keys.items():
            valid = (
                valid_root
                and type(semantic_key) is tuple
                and len(semantic_key) in (3, 4)
                and type(semantic_key[0]) is str
                and (
                    (
                        semantic_key[0] == "power"
                        and len(semantic_key) == 4
                        and type(semantic_key[1]) is ActionProgramID
                        and type(semantic_key[2]) is int
                        and semantic_key[2] >= 1
                        and type(semantic_key[3]) is TemporalCocycle
                    )
                    or (
                        semantic_key[0] == "compose"
                        and len(semantic_key) == 3
                        and type(semantic_key[1]) is FieldCellActionID
                        and type(semantic_key[2]) is FieldCellActionID
                    )
                )
                and type(index) is int
                and 0 <= index < state.next_action
                and state.actions.get(index) is not None
            )
            try:
                if semantic_key[0] == "power":
                    kernel_id = semantic_key[1]
                    if type(kernel_id) is not ActionProgramID:
                        raise TypeError("power key requires a kernel identity")
                    adapter.kernels.kernel(kernel_id)
                valid &= semantic_key == expected_keys.get(index)
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.add(id(semantic_key))
            else:
                invalid.add((state.action_key_owner, id(semantic_key)))
        for composition_key, index in state.compositions.items():
            valid = (
                valid_root
                and type(composition_key) is tuple
                and len(composition_key) == 2
                and all(type(item) is FieldCellActionID for item in composition_key)
                and type(index) is int
                and 0 <= index < state.next_action
            )
            try:
                before, after = composition_key
                adapter.validate_action(before)
                adapter.validate_action(after)
                record = state.actions[index]
                first = state.actions[before.local_id]
                second = state.actions[after.local_id]
                homogeneous = (
                    first.kernel == second.kernel
                    and expected_keys.get(before.local_id, (None,))[0] == "power"
                    and expected_keys.get(after.local_id, (None,))[0] == "power"
                )
                expected_composite = (
                    (
                        "power",
                        second.kernel,
                        first.repetitions + second.repetitions,
                        record.cocycle,
                    )
                    if homogeneous
                    else ("compose", before, after)
                )
                valid &= (
                    expected_keys.get(index) == expected_composite
                    and record.kernel == second.kernel
                    and record.signature == second.signature
                    and record.repetitions == first.repetitions + second.repetitions
                    and record.cocycle
                    == TemporalCocycle(
                        first.cocycle.physical_ticks + second.cocycle.physical_ticks,
                        first.cocycle.event_weight + second.cocycle.event_weight,
                        first.cocycle.frame_shift + second.cocycle.frame_shift,
                    )
                )
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.add(id(composition_key))
            else:
                invalid.add((state.compose_owner, id(composition_key)))
        expected_leaf_reverse: dict[LocalInterfaceID, int] = {}
        for interface, blank in state.leaf_records.items():
            if type(interface) is LeafProductKey:
                valid = type(blank) is LocalInterfaceID
                leaf_kernel: PrimitiveKernel | None = None
                try:
                    leaf_kernel = adapter.kernels.kernel(interface.kernel)
                    declaration = adapter.quotients.interface(interface.signature)
                    valid &= (
                        type(interface.symbol) is int
                        and 0 <= interface.symbol <= leaf_kernel.blank
                        and declaration.kernel.behavior
                        == (TILE_KERNEL_CONTRACT, _effect_key(leaf_kernel.effect))
                        and leaf_kernel.blank
                        in signatures.get(interface.signature, set())
                        and declaration.inputs == input_ports_for_kernel(leaf_kernel)
                        and declaration.outputs == output_sorts_for_kernel(leaf_kernel)
                        and declaration.phase_count == 1
                        and declaration.orientations == (0,)
                        and type(blank) is LocalInterfaceID
                        and adapter.quotients.resolve(blank).signature
                        == interface.signature
                        and type(state.leaf_records.get(blank)) is int
                        and state.leaf_records.get(blank) == leaf_kernel.blank
                    )
                except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                    valid = False
                if valid:
                    approved.add(id(interface))
                    assert type(blank) is LocalInterfaceID
                    assert leaf_kernel is not None
                    expected_leaf_reverse[blank] = leaf_kernel.blank
                else:
                    invalid.add((state.leaf_owner, id(interface)))
                continue
            if type(interface) is not LocalInterfaceID:
                invalid.add((state.leaf_owner, id(interface)))
        for interface, blank in state.leaf_records.items():
            if type(interface) is LeafProductKey:
                continue
            if type(interface) is not LocalInterfaceID:
                invalid.add((state.leaf_owner, id(interface)))
                continue
            valid = type(blank) is int
            try:
                signature = adapter.quotients.resolve(interface).signature
                valid &= (
                    blank in signatures.get(signature, set())
                    and expected_leaf_reverse.get(interface) == blank
                )
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.add(id(interface))
            else:
                invalid.add((state.leaf_owner, id(interface)))
        if adapter.results is not None:
            result_state = adapter.results.audit_snapshot()
            if (
                result_state.ledger is not ledger
                or id(containers.get(result_state.memo_owner))
                != result_state.memo_store_identity
            ):
                invalid.add((result_state.memo_owner, id(adapter.results)))
            for key, result in result_state.memo.items():
                if type(key) is SpatialInterfaceKey:
                    continue
                if type(key) is NormalizedRegionKey:
                    if type(result) is not NormalizedRegionResult:
                        invalid.add((result_state.memo_owner, id(key)))
                    continue
                if type(key) is BoundaryConcatKey:
                    if type(result) is not BoundaryConcatResult:
                        invalid.add((result_state.memo_owner, id(key)))
                    continue
                if type(key) is SourceRootMatchKey:
                    valid = type(result) is RootMatchResult and (
                        valid_source_root_match_record(adapter, key, result)
                    )
                    if not valid:
                        invalid.add((result_state.memo_owner, id(key)))
                    continue
                if type(key) is ReverseThresholdSummaryKey:
                    if type(result) is not BlockSummary:
                        invalid.add((result_state.memo_owner, id(key)))
                        continue
                    valid = True
                    try:
                        key.__post_init__()
                        node = adapter.tiles.resolve(key.input)
                        alphabet = adapter.tiles.alphabet(node.alphabet)
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
                    except (
                        TypeError,
                        ValueError,
                        KeyError,
                        AttributeError,
                        IndexError,
                    ):
                        valid = False
                    if not valid:
                        invalid.add((result_state.memo_owner, id(key)))
                    continue
                if type(key) is ReverseBoundOutputKey:
                    valid = valid_reverse_bound_output(adapter.results, key, result)
                    if not valid:
                        invalid.add((result_state.memo_owner, id(key)))
                    continue
                execution_key = cast(
                    PoweredResultKey
                    | PoweredInterfaceKey
                    | FusedInterfaceKey
                    | CausalInterfaceKey
                    | DirectedTransferKey
                    | BehaviorBindingKey,
                    key,
                )
                valid = type(execution_key) in (
                    PoweredResultKey,
                    PoweredInterfaceKey,
                    FusedInterfaceKey,
                    CausalInterfaceKey,
                    DirectedTransferKey,
                    BehaviorBindingKey,
                )
                try:
                    kernel = adapter.kernels.kernel(
                        adapter.action_record(execution_key.action).kernel,
                    )
                    expected = TileAlphabet(
                        kernel.blank + 1,
                        kernel.blank,
                        kernel.base,
                        max(1, kernel.blank.bit_length()),
                        "unsigned-radix-cell-with-explicit-blank",
                        CANONICAL_TILE_ALPHABET_VERSION,
                    )

                    valid &= _matches_alphabet(adapter, expected, execution_key.input)
                    if type(result) is CompletedResult:
                        valid &= _matches_alphabet(adapter, expected, result.output)
                    elif type(execution_key) is CausalInterfaceKey:
                        valid &= type(result) is CompletedInterfaceResult and (
                            valid_causal_interface_record(
                                adapter,
                                adapter_scheduler,
                                execution_key,
                                result,
                            )
                        )
                    elif type(execution_key) is DirectedTransferKey:
                        valid &= type(result) is int
                    elif type(execution_key) is BehaviorBindingKey:
                        valid &= type(result) is CompletedBehaviorClassification
                except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                    valid = False
                if not valid:
                    invalid.add((result_state.memo_owner, id(execution_key)))
        if valid_root and not any(
            owner == item[0] for item in invalid for owner, _ in stores
        ):
            approved.update(id(store) for _, store in stores)

    def valid_tile_lease(lease: object, tiles: TileArena, *, open_: bool) -> bool:
        if type(lease) is not TileLease:
            return False
        snapshot = lease.audit_snapshot()
        if snapshot.arena is not tiles:
            return False
        if type(snapshot.closed) is not bool or snapshot.closed is open_:
            return False
        if type(snapshot.identity) is not int:
            return False
        if not open_:
            return True
        try:
            tiles.resolve(lease.tile)
        except (TypeError, ValueError, KeyError, AttributeError, IndexError):
            return False
        return True

    def valid_result_lease(
        lease: object,
        scheduler: TileScheduler,
        key: PoweredResultKey,
    ) -> bool:
        if type(lease) is not ResultLease:
            return False
        snapshot = lease.audit_snapshot()
        if type(snapshot.result) is not CompletedResult:
            return False
        if (
            snapshot.issuer is not scheduler.results
            or type(snapshot.key) is not PoweredResultKey
        ):
            return False
        if snapshot.key != key:
            return False
        if not valid_request(scheduler, key) or not valid_tile_lease(
            snapshot.tile, scheduler.tiles, open_=True
        ):
            return False
        try:
            result = snapshot.result
            result.__post_init__()
            output = scheduler.tiles.resolve(result.output)
            scheduler.results.validate_output(key.action, result.output)
            outgoing = scheduler.results.interfaces.resolve(result.outgoing)
            boundary_ids = scheduler.results.result_tile_ids(result)[1:]
            return (
                snapshot.closed is False
                and snapshot.tile.tile == result.output
                and type(snapshot.boundary_tiles) is tuple
                and all(
                    valid_tile_lease(value, scheduler.tiles, open_=True)
                    for value in snapshot.boundary_tiles
                )
                and tuple(value.tile for value in snapshot.boundary_tiles)
                == boundary_ids
                and result.relative_extent == output.extent
                and result.relative_extent <= output.width
                and outgoing.signature == key.wiring.signature
                and valid_ports(scheduler, outgoing.signature, result.outgoing_ports)
                and (
                    result.observed_input_ports is None
                    or valid_ports(
                        scheduler,
                        key.wiring.signature,
                        result.observed_input_ports,
                    )
                )
                and valid_boundaries(
                    scheduler,
                    result.outgoing_boundaries,
                    result.output,
                )
            )
        except (TypeError, ValueError, KeyError, AttributeError, IndexError):
            return False

    application_by_scheduler: dict[TileScheduler, dict[int, TileApplication]] = {}
    for application in applications:
        snapshot = application.audit_snapshot()
        scheduler = snapshot.scheduler
        scheduler_state = scheduler.audit_snapshot()
        valid = (
            type(scheduler) is TileScheduler
            and scheduler in physical_schedulers
            and type(snapshot.identity) is int
            and type(scheduler_state.next_application) is int
            and 0 <= snapshot.identity < scheduler_state.next_application
            and type(snapshot.closed) is bool
        )
        try:
            if snapshot.closed:
                valid &= valid_tile_lease(
                    snapshot.input_lease, scheduler.tiles, open_=False
                )
                if snapshot.root_lease is not None:
                    valid &= (
                        type(snapshot.root_lease) is ResultLease
                        and snapshot.root_lease.audit_snapshot().closed is True
                    )
            else:
                valid &= valid_tile_lease(
                    snapshot.input_lease, scheduler.tiles, open_=True
                )
                source = snapshot.input_lease.tile
                key = PoweredResultKey(
                    snapshot.action,
                    source,
                    snapshot.ports,
                    snapshot.wiring,
                )
                valid &= valid_request(scheduler, key)
                if snapshot.root_lease is not None:
                    valid &= valid_result_lease(snapshot.root_lease, scheduler, key)
                    approved.add(id(snapshot.root_lease))
        except (TypeError, ValueError, KeyError, AttributeError, IndexError):
            valid = False
        if valid:
            previous = application_by_scheduler.setdefault(scheduler, {}).get(
                snapshot.identity,
            )
            if previous is not None and previous is not application:
                valid = False
            else:
                application_by_scheduler[scheduler][snapshot.identity] = application
        if valid:
            approved.add(id(application))
        else:
            invalid.add((-1, id(application)))

    for scheduler in schedulers:
        scheduler_state = scheduler.audit_snapshot()
        if scheduler_state.source_only:
            valid_source_root, source_core = (
                scheduler_support.valid_source_only_scheduler(
                    scheduler, ledger, containers, roots
                )
            )
            if valid_source_root:
                approved.add(id(scheduler))
                if source_core is not None:
                    approved.add(id(source_core))
            else:
                invalid.add((-1, id(scheduler)))
            continue
        owners = scheduler.audit_causal_owners()
        spatial, tasks = owners.spatial, owners.tasks
        spatial_state = scheduler_state.causal_workspace
        task_state = scheduler_state.causal_tasks
        if spatial_state is None or task_state is None:
            invalid.add((-1, id(scheduler)))
            continue
        valid_root = (
            scheduler.ledger is ledger
            and scheduler.tiles.ledger is ledger
            and scheduler.results.ledger is ledger
            and scheduler_state.ledger is ledger
            and scheduler_state.pin_owner is not None
            and scheduler_state.pin_store is not None
            and id(containers.get(scheduler_state.pin_owner))
            == id(scheduler_state.pin_store)
            and type(spatial) is CausalSpatialWorkspace
            and spatial.ledger is ledger
            and spatial_state.owner == spatial.owner
            and id(containers.get(spatial_state.owner))
            == id(spatial_state.reference_store)
            and id(containers.get(spatial_state.buffer_owner))
            == id(spatial_state.buffer_store)
            and type(tasks) is CausalTaskWorkspace
            and tasks.ledger is ledger
            and task_state.workspace is tasks
            and id(containers.get(task_state.memo_owner)) == id(task_state.memo_store)
            and id(containers.get(task_state.active_owner))
            == id(task_state.active_store)
            and id(containers.get(task_state.action_pending_owner))
            == id(task_state.pending_store)
            and id(containers.get(task_state.action_admitted_owner))
            == id(task_state.admitted_store)
            and id(containers.get(task_state.frames.owner))
            == id(task_state.frames.store)
            and id(containers.get(task_state.summary_frames.owner))
            == id(task_state.summary_frames.store)
            and task_state.frames.owner != task_state.summary_frames.owner
            and _has_distinct_identity(
                task_state.frames.store,
                task_state.summary_frames.store,
            )
            and id(containers.get(task_state.values.owner))
            == id(task_state.values.store)
            and id(containers.get(task_state.directed_frames.owner))
            == id(task_state.directed_frames.store)
            and id(containers.get(task_state.directed_values.owner))
            == id(task_state.directed_values.store)
            and scheduler.results.causal_tasks is tasks
            and type(scheduler_state.next_application) is int
            and scheduler_state.next_application >= 0
        )
        live = application_by_scheduler.get(scheduler, {})
        registry_approved, registry_invalid = scheduler.audit_application_registry(
            containers
        )
        approved.update(registry_approved)
        invalid.update(registry_invalid)
        valid_root &= scheduler.audit_application_bindings(live)
        for binding, lease in scheduler_state.pins.items():
            valid = valid_root and type(binding) is tuple and len(binding) == 2
            try:
                application_id, key = binding
                valid &= (
                    type(application_id) is int
                    and type(key) is PoweredResultKey
                    and application_id in live
                    and not live[application_id].audit_snapshot().closed
                    and valid_result_lease(lease, scheduler, key)
                )
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.update((id(binding), id(lease)))
            else:
                invalid.add((scheduler_state.pin_owner or -1, id(binding)))
        workspace_approved, workspace_invalid = causal_inventory.audit_task_workspace(
            scheduler,
            spatial,
            tasks,
            valid_root,
        )
        approved.update(workspace_approved)
        invalid.update(workspace_invalid)

    from number_compiler.resources.tile_radix_inventory import (
        audit_tile_radix_runtime,
    )

    radix_approved, radix_invalid = audit_tile_radix_runtime(
        ledger,
        containers,
        roots,
        physical_schedulers,
        applications,
    )
    approved.update(radix_approved)
    invalid.update(radix_invalid)
    for root in roots:
        if type(root) is LazyProjection:
            projection_snapshot = root.audit_snapshot()
            valid = (
                projection_snapshot.ledger is ledger
                and type(projection_snapshot.scheduler) is TileScheduler
                and projection_snapshot.scheduler in physical_schedulers
                and type(projection_snapshot.application) is TileApplication
                and projection_snapshot.application.scheduler
                is projection_snapshot.scheduler
                and type(projection_snapshot.logical_extent) is int
                and projection_snapshot.logical_extent >= 1
                and type(projection_snapshot.closed) is bool
                and projection_snapshot.closed
                == projection_snapshot.application.audit_snapshot().closed
            )
            if valid:
                approved.add(id(root))
            else:
                invalid.add((-1, id(root)))
    return approved, invalid


__all__ = ["audit_tile_runtime"]
