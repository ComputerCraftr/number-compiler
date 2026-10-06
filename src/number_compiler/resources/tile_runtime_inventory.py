"""Independent ownership audit for the canonical tile execution runtime."""

from __future__ import annotations

from collections.abc import Mapping
from sys import getsizeof
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
from number_compiler.hashlife.execution.tile_application_authority import (
    audit_tile_application_registry,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame,
    CausalPrefix,
)
from number_compiler.hashlife.execution.tile_fused_kernel import LeafProductKey
from number_compiler.hashlife.execution.tile_kernel import (
    PrimitiveTileKernelAdapter,
)
from number_compiler.hashlife.execution.tile_kernel_contract import (
    TILE_KERNEL_CONTRACT,
)
from number_compiler.hashlife.execution.tile_scheduler import (
    TileApplication,
    TileScheduler,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
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
    CausalFrameStack,
    CausalResultStack,
    CausalSpatialWorkspace,
    CausalTaskWorkspace,
    CausalValueStack,
    SpatialReferenceBuffer,
)
from number_compiler.resources.fused_traversal_inventory import (
    audit_fused_traversal_workspace,
)
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit
from number_compiler.resources.reverse_morphism_inventory import audit_reverse_morphisms
from number_compiler.resources.reverse_residual_inventory import audit_reverse_residuals
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
        scheduler for scheduler in schedulers if not scheduler._source_only
    )
    applications = tuple(root for root in roots if type(root) is TileApplication)

    for adapter in adapters:
        adapter_scheduler = next(
            (
                scheduler
                for scheduler in physical_schedulers
                if scheduler.adapter is adapter and scheduler.results is adapter.results
            ),
            None,
        )
        stores = (
            (adapter._action_owner, adapter._actions),
            (adapter._action_key_owner, adapter._action_keys),
            (adapter._leaf_owner, adapter._leaf_records),
            (adapter._compose_owner, adapter._compositions),
        )
        valid_root = (
            adapter.ledger is ledger
            and adapter.tiles.ledger is ledger
            and adapter.kernels.ledger is ledger
            and adapter.quotients.ledger is ledger
            and all(containers.get(owner) is store for owner, store in stores)
            and type(adapter._next_action) is int
            and adapter._next_action >= 0
        )
        fused_approved, fused_invalid = audit_fused_traversal_workspace(
            adapter,
            containers,
        )
        approved.update(fused_approved)
        invalid.update(fused_invalid)
        valid_root &= not fused_invalid
        signatures: dict[PortSignatureID, set[int]] = {}
        expected_keys: dict[int, ActionSemanticKey] = {}
        for index, record in adapter._actions.items():
            valid = valid_root and type(index) is int and type(record) is _Action
            try:
                if not 0 <= index < adapter._next_action:
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
                    and declaration.inputs == adapter._ports(kernel)
                    and declaration.outputs == adapter._output_sorts(kernel)
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
                    first = adapter._actions[before.local_id]
                    second = adapter._actions[after.local_id]
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
                mapped = adapter._action_keys.get(expected_key)
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
                invalid.add((adapter._action_owner, id(record)))
        for semantic_key, index in adapter._action_keys.items():
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
                and 0 <= index < adapter._next_action
                and adapter._actions.get(index) is not None
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
                invalid.add((adapter._action_key_owner, id(semantic_key)))
        for composition_key, index in adapter._compositions.items():
            valid = (
                valid_root
                and type(composition_key) is tuple
                and len(composition_key) == 2
                and all(type(item) is FieldCellActionID for item in composition_key)
                and type(index) is int
                and 0 <= index < adapter._next_action
            )
            try:
                before, after = composition_key
                adapter.validate_action(before)
                adapter.validate_action(after)
                record = adapter._actions[index]
                first = adapter._actions[before.local_id]
                second = adapter._actions[after.local_id]
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
                invalid.add((adapter._compose_owner, id(composition_key)))
        expected_leaf_reverse: dict[LocalInterfaceID, int] = {}
        for interface, blank in adapter._leaf_records.items():
            if type(interface) is LeafProductKey:
                valid = type(blank) is LocalInterfaceID
                try:
                    kernel = adapter.kernels.kernel(interface.kernel)
                    declaration = adapter.quotients.interface(interface.signature)
                    valid &= (
                        type(interface.symbol) is int
                        and 0 <= interface.symbol <= kernel.blank
                        and declaration.kernel.behavior
                        == (TILE_KERNEL_CONTRACT, _effect_key(kernel.effect))
                        and kernel.blank in signatures.get(interface.signature, set())
                        and declaration.inputs == adapter._ports(kernel)
                        and declaration.outputs == adapter._output_sorts(kernel)
                        and declaration.phase_count == 1
                        and declaration.orientations == (0,)
                        and type(blank) is LocalInterfaceID
                        and adapter.quotients.resolve(blank).signature
                        == interface.signature
                        and type(adapter._leaf_records.get(blank)) is int
                        and adapter._leaf_records.get(blank) == kernel.blank
                    )
                except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                    valid = False
                if valid:
                    approved.add(id(interface))
                    assert type(blank) is LocalInterfaceID
                    expected_leaf_reverse[blank] = kernel.blank
                else:
                    invalid.add((adapter._leaf_owner, id(interface)))
                continue
            if type(interface) is not LocalInterfaceID:
                invalid.add((adapter._leaf_owner, id(interface)))
        for interface, blank in adapter._leaf_records.items():
            if type(interface) is LeafProductKey:
                continue
            if type(interface) is not LocalInterfaceID:
                invalid.add((adapter._leaf_owner, id(interface)))
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
                invalid.add((adapter._leaf_owner, id(interface)))
        if adapter.results is not None:
            for key, result in adapter.results._memo.items():
                if type(key) is SpatialInterfaceKey:
                    continue
                if type(key) is NormalizedRegionKey:
                    if type(result) is not NormalizedRegionResult:
                        invalid.add((adapter.results._memo_owner, id(key)))
                    continue
                if type(key) is BoundaryConcatKey:
                    if type(result) is not BoundaryConcatResult:
                        invalid.add((adapter.results._memo_owner, id(key)))
                    continue
                if type(key) is SourceRootMatchKey:
                    valid = type(result) is RootMatchResult and (
                        valid_source_root_match_record(adapter, key, result)
                    )
                    if not valid:
                        invalid.add((adapter.results._memo_owner, id(key)))
                    continue
                if type(key) is ReverseThresholdSummaryKey:
                    if type(result) is not BlockSummary:
                        invalid.add((adapter.results._memo_owner, id(key)))
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
                            and alphabet.version == "canonical-tile-alphabet-v1"
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
                        invalid.add((adapter.results._memo_owner, id(key)))
                    continue
                if type(key) is ReverseBoundOutputKey:
                    valid = valid_reverse_bound_output(adapter.results, key, result)
                    if not valid:
                        invalid.add((adapter.results._memo_owner, id(key)))
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
                        adapter._action(execution_key.action).kernel,
                    )
                    expected = TileAlphabet(
                        kernel.blank + 1,
                        kernel.blank,
                        kernel.base,
                        max(1, kernel.blank.bit_length()),
                        "unsigned-radix-cell-with-explicit-blank",
                        "canonical-tile-alphabet-v1",
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
                    invalid.add((adapter.results._memo_owner, id(execution_key)))
        if valid_root and not any(
            owner == item[0] for item in invalid for owner, _ in stores
        ):
            approved.update(id(store) for _, store in stores)

    def valid_tile_lease(lease: object, tiles: TileArena, *, open_: bool) -> bool:
        if type(lease) is not TileLease or lease._arena is not tiles:
            return False
        if type(lease._closed) is not bool or lease._closed is open_:
            return False
        if type(lease._id) is not int:
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
        if type(lease) is not ResultLease or type(lease._result) is not CompletedResult:
            return False
        if (
            lease._issuer is not scheduler.results
            or type(lease._key) is not PoweredResultKey
        ):
            return False
        if lease._key != key:
            return False
        if not valid_request(scheduler, key) or not valid_tile_lease(
            lease._tile, scheduler.tiles, open_=True
        ):
            return False
        try:
            result = lease._result
            result.__post_init__()
            output = scheduler.tiles.resolve(result.output)
            if scheduler.results._validate_output is not None:
                scheduler.results._validate_output(key.action, result.output)
            outgoing = scheduler.results.interfaces.resolve(result.outgoing)
            boundary_ids = scheduler.results._result_tile_ids(result)[1:]
            return (
                lease._closed is False
                and lease._tile.tile == result.output
                and type(lease._boundary_tiles) is tuple
                and all(
                    valid_tile_lease(value, scheduler.tiles, open_=True)
                    for value in lease._boundary_tiles
                )
                and tuple(value.tile for value in lease._boundary_tiles) == boundary_ids
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
        scheduler = application.scheduler
        valid = (
            type(scheduler) is TileScheduler
            and scheduler in physical_schedulers
            and type(application.identity) is int
            and 0 <= application.identity < scheduler._next_application
            and type(application._closed) is bool
        )
        try:
            if application._closed:
                valid &= valid_tile_lease(
                    application._input, scheduler.tiles, open_=False
                )
                if application._root is not None:
                    valid &= (
                        type(application._root) is ResultLease
                        and application._root._closed is True
                    )
            else:
                valid &= valid_tile_lease(
                    application._input, scheduler.tiles, open_=True
                )
                source = application._input.tile
                key = PoweredResultKey(
                    application.action,
                    source,
                    application.ports,
                    application.wiring,
                )
                valid &= valid_request(scheduler, key)
                if application._root is not None:
                    valid &= valid_result_lease(application._root, scheduler, key)
                    approved.add(id(application._root))
        except (TypeError, ValueError, KeyError, AttributeError, IndexError):
            valid = False
        if valid:
            previous = application_by_scheduler.setdefault(scheduler, {}).get(
                application.identity,
            )
            if previous is not None and previous is not application:
                valid = False
            else:
                application_by_scheduler[scheduler][application.identity] = application
        if valid:
            approved.add(id(application))
        else:
            invalid.add((-1, id(application)))

    for scheduler in schedulers:
        if scheduler._source_only:
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
        spatial = scheduler._causal_workspace
        tasks = scheduler._causal_tasks
        valid_root = (
            scheduler.ledger is ledger
            and scheduler.tiles.ledger is ledger
            and scheduler.results.ledger is ledger
            and containers.get(scheduler._pin_owner) is scheduler._pins
            and type(spatial) is CausalSpatialWorkspace
            and spatial.ledger is ledger
            and containers.get(spatial.owner) is spatial._refs
            and containers.get(spatial.buffer_owner) is spatial._buffers
            and type(tasks) is CausalTaskWorkspace
            and tasks.ledger is ledger
            and containers.get(tasks.memo_owner) is tasks.memo
            and containers.get(tasks.active_owner) is tasks.active
            and containers.get(tasks.action_pending_owner) is tasks.action_pending
            and containers.get(tasks.action_admitted_owner) is tasks.action_admitted
            and type(tasks.frames) is CausalFrameStack
            and tasks.frames.ledger is ledger
            and containers.get(tasks.frames.owner) is tasks.frames._frames
            and type(tasks.values) is CausalResultStack
            and tasks.values.ledger is ledger
            and containers.get(tasks.values.owner) is tasks.values._values
            and type(tasks.directed_frames) is CausalFrameStack
            and tasks.directed_frames.ledger is ledger
            and containers.get(tasks.directed_frames.owner)
            is tasks.directed_frames._frames
            and type(tasks.directed_values) is CausalValueStack
            and tasks.directed_values.ledger is ledger
            and containers.get(tasks.directed_values.owner)
            is tasks.directed_values._values
            and scheduler.results._causal_tasks is tasks
            and type(scheduler._next_application) is int
            and scheduler._next_application >= 0
        )
        live = application_by_scheduler.get(scheduler, {})
        registry_approved, registry_invalid = audit_tile_application_registry(
            scheduler._applications,
            containers,
        )
        approved.update(registry_approved)
        invalid.update(registry_invalid)
        valid_root &= set(scheduler._applications.records) == set(live) and all(
            cleanup.application() is live[identity]
            for identity, cleanup in scheduler._applications.records.items()
        )
        for binding, lease in scheduler._pins.items():
            valid = valid_root and type(binding) is tuple and len(binding) == 2
            try:
                application_id, key = binding
                valid &= (
                    type(application_id) is int
                    and type(key) is PoweredResultKey
                    and application_id in live
                    and not live[application_id]._closed
                    and valid_result_lease(lease, scheduler, key)
                )
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.update((id(binding), id(lease)))
            else:
                invalid.add((scheduler._pin_owner, id(binding)))
        expected_refs: set[tuple[int, int]] = set()
        capacities = object_bytes = 0
        for identity, buffer in spatial._buffers.items():
            valid = (
                valid_root
                and type(identity) is int
                and type(buffer) is SpatialReferenceBuffer
            )
            try:
                valid &= (
                    buffer.workspace is spatial
                    and buffer.identity == identity
                    and type(buffer.capacity) is int
                    and type(buffer.used) is int
                    and 0 <= buffer.used <= buffer.capacity
                    and type(buffer.closed) is bool
                    and not buffer.closed
                    and type(buffer.backing_bytes) is int
                    and buffer.backing_bytes
                    == getsizeof(buffer) + buffer.capacity * getsizeof((0, 0))
                )
                capacities += buffer.capacity
                object_bytes += buffer.backing_bytes
                for index in range(buffer.capacity):
                    ref_key = (identity, index)
                    expected_refs.add(ref_key)
                    value = spatial._refs[ref_key]
                    valid_value = value is None and index >= buffer.used
                    if index < buffer.used and type(value) is int:
                        valid_value = value >= 0
                    elif index < buffer.used and type(value) is TileID:
                        scheduler.tiles.resolve(value)
                        valid_value = True
                    elif index < buffer.used and type(value) is CausalPrefix:
                        scheduler.adapter.validate_action(value.action)
                        valid_value = (
                            type(value.side) is int
                            and value.side in (0, 1)
                            and type(value.producer_seed) is int
                            and value.producer_seed >= 0
                            and type(value.consumer_seed) is int
                            and value.consumer_seed >= 0
                            and type(value.explicit_edge) is bool
                        )
                        for view in (value.view, value.consumer_view):
                            if view is not None:
                                view.__post_init__()
                                tile_record = scheduler.tiles.resolve(view.tile)
                                valid_value &= (
                                    view.source_offset + view.relative_extent
                                    <= tile_record.width
                                )
                    valid &= valid_value
                    if valid_value:
                        approved.update((id(ref_key), id(value)))
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
            if valid:
                approved.update((id(identity), id(buffer)))
            else:
                invalid.add((spatial.buffer_owner, id(buffer)))
        valid_root &= (
            set(spatial._refs) == expected_refs
            and spatial.slots == capacities
            and spatial._object_bytes == object_bytes
            and type(spatial._next) is int
            and spatial._next >= 0
            and all(identity < spatial._next for identity in spatial._buffers)
        )
        if not valid_root:
            invalid.add((spatial.owner, id(spatial)))

        task_approved, task_invalid = causal_inventory.audit_task_payloads(
            scheduler, tasks, valid_root
        )
        approved.update(task_approved)
        invalid.update(task_invalid)
        frame_references = 0
        for frame in tasks.frames._frames:
            valid = (
                valid_root
                and type(frame) is CausalFrame
                and type(frame.op) is str
                and frame.op in scheduler_support.CAUSAL_FRAME_OPS
                and type(frame.args) is tuple
                and len(frame.args) <= 8
                and type(frame.saved) is tuple
                and len(frame.saved) <= 3
                and type(frame.stage) is int
                and frame.stage >= -1
                and type(frame.memoized) is bool
                and causal_inventory.valid_frame_value(scheduler, frame.args, approved)
                and causal_inventory.valid_frame_value(scheduler, frame.saved, approved)
            )
            frame_references += len(frame.args) + len(frame.saved)
            if valid:
                approved.add(id(frame))
            else:
                invalid.add((tasks.frames.owner, id(frame)))
        valid_root &= tasks.frames.payload_references == frame_references
        if not valid_root:
            invalid.add((tasks.frames.owner, id(tasks.frames)))
        for value in tasks.values._values:
            if valid_root and causal_inventory.valid_frame_value(
                scheduler, value, approved
            ):
                approved.add(id(value))
            else:
                invalid.add((tasks.values.owner, id(value)))
        if valid_root:
            approved.update(
                (
                    id(scheduler),
                    id(scheduler._pins),
                    id(spatial),
                    id(spatial._refs),
                    id(spatial._buffers),
                    id(tasks),
                    id(tasks.memo),
                    id(tasks.active),
                    id(tasks.frames),
                    id(tasks.frames._frames),
                    id(tasks.values),
                    id(tasks.values._values),
                )
            )

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
            valid = (
                root.ledger is ledger
                and type(root.scheduler) is TileScheduler
                and root.scheduler in physical_schedulers
                and type(root._application) is TileApplication
                and root._application.scheduler is root.scheduler
                and type(root._logical_extent) is int
                and root._logical_extent >= 1
                and type(root._closed) is bool
                and root._closed == root._application._closed
            )
            if valid:
                approved.add(id(root))
            else:
                invalid.add((-1, id(root)))
    return approved, invalid


__all__ = ["audit_tile_runtime"]
