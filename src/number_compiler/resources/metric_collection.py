"""Schema-eight metric collection from one immutable ledger snapshot."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import fields, replace
from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.cache_gc_metrics import cache_event_histograms
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_records import (
    HashLifeProjectionMetrics,
    LedgerMetrics,
)
from number_compiler.resources.metric_registry import (
    ALGEBRAIC_FIELD_WORK_COUNTERS,
    DIAMOND_MEMO_ROLES,
    DIAMOND_WORK_COUNTERS,
    QUOTIENT_WORK_COUNTERS,
    SEMANTIC_ADAPTER_WORK_COUNTERS,
    observed_node_partition,
    schema7_inventory_values,
    schema7_work_values,
)
from number_compiler.resources.metric_replace import replace_metric
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.payload_policy import _role
from number_compiler.resources.semantic_metric_registry import (
    SEMANTIC_OUTCOME_COUNTERS,
)
from number_compiler.resources.temporal_diagnostics import (
    collect_temporal_diagnostics,
)


def collect_ledger_metrics(
    ledger: ResourceLedger, *, audit_payloads: bool = True
) -> LedgerMetrics:
    """Collect resource counts, optionally performing explicit graph audits.

    Public runtime metric snapshots pass ``audit_payloads=False``. Deep payload
    and ownership walks remain available to callers that explicitly request a
    ledger audit.
    """
    from number_compiler.arithmetic.carry.reverse_port_functions import (
        ReversePortFunction,
    )
    from number_compiler.arithmetic.carry.reverse_sector_transfer import (
        ReverseCarrySectorTransfer,
    )
    from number_compiler.hashlife.actions.tile_action_algebra import (
        retained_action_nodes,
    )
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileApplication
    from number_compiler.hashlife.interfaces.diamond_kernel import (
        DiamondKernelArena,
        FiniteExpression,
        PrimitiveKernel,
    )
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
        LocalInterfaceID,
    )
    from number_compiler.hashlife.tiles.tile_boundaries import (
        BoundaryTileOperands,
        BoundaryTileView,
    )
    from number_compiler.hashlife.tiles.tile_result_records import (
        CausalInterfaceKey,
        CompletedResult,
        FusedInterfaceKey,
        NormalizedRegionKey,
        NormalizedRegionResult,
        PoweredInterfaceKey,
        PoweredResultKey,
        SpatialInterfaceKey,
    )
    from number_compiler.hashlife.tiles.tile_results import (
        CompletedResultArena,
        ResultLease,
    )
    from number_compiler.hashlife.tiles.tiles import TileArena, TileID
    from number_compiler.projection.point_response import PointResponse
    from number_compiler.resources.ownership import OwnershipAudit
    from number_compiler.resources.payload_policy import PayloadAudit

    source_version = ledger.mutation_version
    snapshot = ledger.snapshot()
    root_signature = ledger.audit_root_signature() if not audit_payloads else None
    cached_audit = ledger.cached_payload_audit(root_signature)
    audit_is_current = type(cached_audit) is PayloadAudit
    if audit_payloads:
        # Audits charge their bounded arithmetic; the retained inventory stays fixed.
        audit = audit_registered_payloads(ledger, snapshot=snapshot, fresh=False)
        audit_is_current = True
    elif type(cached_audit) is PayloadAudit:
        audit = cached_audit
    else:
        audit = PayloadAudit(0, 0, 0)
    audit_counters = {
        "reverse_pair_output_audit_entries",
        "reverse_payload_audit_identity_operand_bits",
        "collatz_d8_payload_audit_local_symbols",
        "dyadic_payload_audit_branch_steps",
        "dyadic_payload_audit_operand_bits",
        "dyadic_payload_audit_cycle_checks",
        "dyadic_payload_audit_compositions",
        "dyadic_payload_audit_prefix_additions",
        "dyadic_payload_audit_reconstruction_hits",
        "source_image_seal_validation_visits",
        "mahler_source_validation_operand_bits",
        "antihydra_payload_audit_branch_steps",
        "antihydra_payload_audit_arithmetic_branch_steps",
        "antihydra_payload_audit_compositions",
        "antihydra_payload_audit_physical_steps",
        "antihydra_payload_audit_endpoint_operand_bits",
        "antihydra_payload_audit_projection_fragment_operand_bits",
        "antihydra_payload_audit_projection_fragment_steps",
        "payload_audit_contract_member_visits",
        "payload_audit_contract_dependency_visits",
        "double_reverse_payload_audit_boundary_visits",
        "double_reverse_payload_audit_boundary_classifications",
        "comma_boundary_explicit_audit_component_checks",
        "comma_boundary_explicit_audit_operand_bits",
    }
    if audit_payloads:
        # Occurrence binding validation reaches the ordinary identity validator.
        # Its bounded checks are charged audit work; they may not allocate or
        # publish anything (the mutation-version check below still enforces that).
        audit_counters.update(
            {
                "reverse_field_action_semantic_identity_requests",
                "reverse_field_action_semantic_identity_cache_hits",
                "reverse_field_action_identity_validation_radial_bit_work",
            }
        )
    if ledger.mutation_version != source_version or any(
        ledger.counters.get(key, 0) != snapshot.counters.get(key, 0)
        for key in ledger.counters.keys() | snapshot.counters.keys()
        if key not in audit_counters
    ):
        raise RuntimeError("execution resources changed during metric projection")
    snapshot = replace(snapshot, counters=dict(ledger.counters))
    execution_roots = tuple(ledger.iter_execution_roots())
    cache_histograms = tuple(
        cache_event_histograms(root._cache_metrics)
        for root in execution_roots
        if type(root) is TileArena and root.ledger is ledger
    )
    if (
        ledger.mutation_version != source_version
        or ledger.counters != snapshot.counters
    ):
        raise RuntimeError("execution resources changed during metric capture")
    inventory = snapshot.inventory
    cached_ownership = ledger.cached_ownership_audit(root_signature)
    ownership_is_current = type(cached_ownership) is OwnershipAudit
    if audit_payloads:
        ownership = audit_execution_ownership(ledger, fresh=False)
        ownership_is_current = True
    elif type(cached_ownership) is OwnershipAudit:
        ownership = cached_ownership
    else:
        ownership = OwnershipAudit(0, 0, ())
    # A zero-population scope is an accounting namespace, not a retained
    # container.  Require inventory and payload callbacks as soon as the owner
    # retains entries, nodes, or roots; do not mark an unused observation scope
    # incomplete merely because it has nothing to enumerate.
    unregistered = (
        sum(
            item.observed_entries is None
            and bool(item.entries or item.nodes or item.roots)
            for item in inventory
        )
        + ownership.unregistered_containers
    )
    unresolved_payloads = sum(
        not item.payloads_registered and bool(item.entries or item.nodes or item.roots)
        for item in inventory
    )
    unknown_nodes = sum(
        item.observed_nodes is None and item.nodes != 0 for item in inventory
    )
    mismatch = sum(item.accounting_delta or 0 for item in inventory)
    counters = snapshot.counters
    cache_levels: dict[str, int] = {}
    cache_spans: dict[str, int] = {}
    for levels, spans in cache_histograms:
        for cache_key, cache_value in levels.items():
            cache_levels[cache_key] = cache_levels.get(cache_key, 0) + cache_value
        for cache_key, cache_value in spans.items():
            cache_spans[cache_key] = cache_spans.get(cache_key, 0) + cache_value
    node_owners = {item.owner for item in inventory if item.observed_nodes}
    actual_records = [
        value
        for owner, container in ledger.iter_containers()
        if owner in node_owners and isinstance(container, (Mapping, Sequence))
        for value in (
            (item for _, item in audit_mapping_items(container))
            if isinstance(container, Mapping)
            else container
        )
    ]
    response_owners = {
        item.owner for item in inventory if _role(item.role) == "observation_memo"
    }
    response_scalars = sum(
        type(value) is PointResponse
        for owner, container in ledger.iter_containers()
        if owner in response_owners and isinstance(container, (Mapping, Sequence))
        for value in (
            (item for _, item in audit_mapping_items(container))
            if isinstance(container, Mapping)
            else container
        )
    )

    reverse_components: list[ReversePortFunction] = []
    reverse_sectors: list[ReverseCarrySectorTransfer] = []
    for root in execution_roots:
        if type(root) is not DiamondQuotientArena or root.ledger is not ledger:
            continue
        for record in root._nodes.values():
            seen: set[int] = set()
            for component in record.components.functions():
                if type(component) is ReversePortFunction and id(component) not in seen:
                    seen.add(id(component))
                    reverse_components.append(component)
            sectors = record.components.reverse_sectors
            if type(sectors) is ReverseCarrySectorTransfer:
                reverse_sectors.append(sectors)

    reverse_coefficient_slots = sum(
        {
            "constant": 1,
            "left-transfer": 5,
            "right-transfer": 2,
            "output": 8,
            "predicate": 0,
        }[component.kind]
        for component in reverse_components
    )
    reverse_limb_slots = sum(
        int(component.kind == "predicate") for component in reverse_components
    )
    reverse_sector_slots = sum(
        1
        + sum(
            len(sector.symbols)
            + sum(len(row) for row in sector.before)
            + sum(len(row) for row in sector.after)
            for sector in summary.sectors
        )
        for summary in reverse_sectors
    )
    unique_reverse_components = {
        id(component): component for component in reverse_components
    }
    unique_reverse_sectors = {id(summary): summary for summary in reverse_sectors}
    unique_reverse_coefficient_slots = sum(
        component.retained_coefficient_slots
        for component in unique_reverse_components.values()
    )
    unique_reverse_limb_slots = sum(
        component.retained_limb_slots
        for component in unique_reverse_components.values()
    )
    unique_reverse_sector_slots = sum(
        summary.retained_slots() for summary in unique_reverse_sectors.values()
    )
    quotient_arenas = tuple(
        root
        for root in execution_roots
        if type(root) is DiamondQuotientArena and root.ledger is ledger
    )
    quotient_records = sum(len(root._nodes) for root in quotient_arenas)

    def nodes_for(*roles: str) -> int:
        return sum(
            item.observed_nodes or 0 for item in inventory if _role(item.role) in roles
        )

    def entries_for(*roles: str) -> int:
        return sum(
            item.observed_entries or 0
            for item in inventory
            if _role(item.role) in roles
        )

    partition = observed_node_partition(inventory, dict(ledger.iter_containers()))
    source_nodes = partition["source_payload_nodes"]
    program_nodes = partition["temporal_program_nodes"]
    canonical_nodes = partition["canonical_transfer_nodes"]
    binding_nodes = partition["spatial_binding_nodes"]
    finite_states = partition["finite_port_state_nodes"]
    endpoint_nodes = partition["exact_endpoint_nodes"]
    other_nodes = partition["other_retained_nodes"]
    interface_records = (
        quotient_records if quotient_arenas else nodes_for("diamond_quotient")
    ) + nodes_for("higher_local_interface")
    observed_entries = sum(item.observed_entries or 0 for item in inventory)
    source_owners = {
        item.owner for item in inventory if _role(item.role) == "exact_source"
    }
    source_objects: set[int] = set()
    source_seen: set[int] = set()
    pending_sources = [
        container
        for owner, container in ledger.iter_containers()
        if owner in source_owners
    ]
    while pending_sources:
        value = pending_sources.pop()
        if id(value) in source_seen:
            continue
        source_seen.add(id(value))
        if type(value) is ExactSource:
            source_objects.add(id(value))
        elif isinstance(value, Mapping):
            pending_sources.extend(item for _, item in audit_mapping_items(value))
        elif isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
            pending_sources.extend(value)
    from number_compiler.hashlife.interfaces.semantic_primitive_macro import (
        PrimitiveMacroArena,
    )
    from number_compiler.hashlife.interfaces.semantic_structures import StructureArena
    from number_compiler.resources.semantic_profile_payload import (
        profile_storage_metrics,
    )

    actual_stores = dict(ledger.iter_containers())
    tile_memo_items: list[tuple[object, object]] = []
    for item in inventory:
        tile_store = actual_stores.get(item.owner)
        if _role(item.role) == "completed_result_memo" and isinstance(
            tile_store, Mapping
        ):
            tile_memo_items.extend(audit_mapping_items(tile_store))
    boundary_tile_references: list[TileID] = []
    boundary_tile_views: list[BoundaryTileView] = []

    def add_boundary_operands(operands: BoundaryTileOperands) -> None:
        if type(operands) is not BoundaryTileOperands:
            return
        for view in (operands.left, operands.right):
            if view is not None:
                boundary_tile_views.append(view)
                boundary_tile_references.append(view.tile)

    for key, value in tile_memo_items:
        if type(key) in (
            PoweredResultKey,
            PoweredInterfaceKey,
            FusedInterfaceKey,
            CausalInterfaceKey,
        ):
            execution_key = cast(
                PoweredResultKey
                | PoweredInterfaceKey
                | FusedInterfaceKey
                | CausalInterfaceKey,
                key,
            )
            add_boundary_operands(execution_key.boundaries)
            if type(execution_key) is FusedInterfaceKey:
                add_boundary_operands(execution_key.consumer_boundaries)
            if (
                type(execution_key) is PoweredResultKey
                and execution_key.fusion is not None
            ):
                add_boundary_operands(execution_key.fusion.producer.boundaries)
                add_boundary_operands(execution_key.fusion.consumer.boundaries)
            if (
                type(execution_key) is CausalInterfaceKey
                and execution_key.fusion is not None
            ):
                add_boundary_operands(execution_key.fusion.producer.boundaries)
                add_boundary_operands(execution_key.fusion.consumer.boundaries)
        if type(value) is CompletedResult:
            add_boundary_operands(value.outgoing_boundaries)
            if value.fusion is not None:
                add_boundary_operands(value.fusion.producer.boundaries)
                add_boundary_operands(value.fusion.consumer.boundaries)
    leased_boundary_views: list[BoundaryTileView] = []
    for root in execution_roots:
        if type(root) is not CompletedResultArena or root.ledger is not ledger:
            continue
        for view, count in root._leased_boundary_operands.records.items():
            if type(view) is BoundaryTileView and type(count) is int and count > 0:
                leased_boundary_views.extend((view,) * count)
    retained_boundary_views = set(boundary_tile_views)
    retained_boundary_views.update(leased_boundary_views)
    primitive_entries = sum(
        len(root.bindings)
        for root in execution_roots
        if type(root) is PrimitiveMacroArena
        and root.ledger is ledger
        and actual_stores.get(root.bindings.owner) is root.bindings._data
    )
    declaration_entries = sum(
        len(root._declarations)
        for root in execution_roots
        if type(root) is StructureArena
        and root.ledger is ledger
        and actual_stores.get(root._declarations.owner) is root._declarations._data
    )
    report = LedgerMetrics(
        **profile_storage_metrics(ledger),
        primitive_macro_cache_entries=primitive_entries,
        semantic_structure_declaration_cache_entries=declaration_entries,
        # Certification of an issued production application is performed by
        # collect_projection_metrics from the live tile stack. A bare ledger
        # cannot self-attest by retaining a retired executor object.
        bimachine_composition_certified=0,
        cache_slots=observed_entries,
        exact_source_occurrences=len(source_objects),
        spatial_occurrence_bindings=sum(
            item.observed_entries or 0
            for item in inventory
            if _role(item.role)
            in (
                "spatial_binding",
                "lazy_field",
                "spatial_parent_memo",
                "diamond_memo",
                "macro_transfer_memo",
                "primitive_spatial_memo",
            )
        ),
        spatial_binding_nodes=binding_nodes,
        canonical_transfer_nodes=canonical_nodes,
        spatial_action_program_nodes=partition["spatial_action_program_nodes"],
        # These are disjoint, role-declared syntax populations within the
        # broader spatial-action partition.  Derive them from the captured
        # inventory rather than importing a retired executor to inspect its
        # private record classes.
        context_program_nodes=nodes_for("context_program"),
        macro_transfer_action_nodes=nodes_for("macro_transfer_program"),
        boundary_expression_program_nodes=nodes_for("boundary_expression_program"),
        unary_function_cache_entries=entries_for("unary_function_memo"),
        image_action_nodes=partition["image_action_nodes"],
        field_image_nodes=nodes_for("field_image"),
        field_interface_nodes=interface_records,
        diamond_cell_nodes=partition["diamond_cell_nodes"],
        primitive_kernel_nodes=sum(
            type(value) is PrimitiveKernel for value in actual_records
        ),
        finite_expression_nodes=sum(
            type(value) is FiniteExpression for value in actual_records
        ),
        temporal_program_nodes=program_nodes,
        finite_port_state_nodes=finite_states,
        other_retained_nodes=other_nodes,
        resource_ledger_entries=snapshot.entries,
        resource_ledger_nodes=snapshot.nodes,
        resource_peak_entries=snapshot.peak_entries,
        resource_peak_nodes=snapshot.peak_nodes,
        resource_observed_entries=sum(item.observed_entries or 0 for item in inventory),
        resource_observed_nodes=sum(item.observed_nodes or 0 for item in inventory),
        resource_unregistered_containers=unregistered,
        resource_unregistered_payload_resolvers=unresolved_payloads,
        resource_accounting_mismatch=mismatch,
        resource_inventory=inventory,
        resource_work_counters=counters,
        resource_workspace_peaks={
            name: value
            for name, value in counters.items()
            if name.endswith("_peak") or "_peak_" in name
        },
        finite_port_applications=counters.get("finite_port_applications", 0),
        finite_port_decision_visits=counters.get("finite_port_decision_visits", 0),
        reverse_carry_function_classifications=counters.get(
            "reverse_carry_function_classifications", 0
        ),
        representation_boundary_complete=int(
            audit_is_current
            and ownership_is_current
            and not (
                unregistered
                or unresolved_payloads
                or unknown_nodes
                or mismatch
                or audit.unknown_payloads
                or audit.forbidden_future_payloads
                or audit.unbounded_future_integers
            )
        ),
        source_payload_nodes=source_nodes,
        action_program_nodes=program_nodes,
        compiler_program_nodes=nodes_for("compiled_action_program"),
        application_program_nodes=nodes_for(
            "action_program", "symbolic_offset_program", "temporal_action"
        ),
        transfer_summary_nodes=canonical_nodes,
        exact_endpoint_nodes=endpoint_nodes,
        retained_point_response_scalars=response_scalars,
        lowering_cache_entries=sum(
            item.entries
            for item in inventory
            if _role(item.role) in ("explicit_lowering", "lowering")
        ),
        forbidden_future_payloads=audit.forbidden_future_payloads,
        retained_unbounded_future_integers=audit.unbounded_future_integers,
        resource_audit_unknown_payloads=audit.unknown_payloads,
        resource_audit_complete=int(
            audit_is_current
            and ownership_is_current
            and not (
                unregistered
                or unresolved_payloads
                or unknown_nodes
                or mismatch
                or audit.unknown_payloads
            )
        ),
        collatz_mul3_summary_requests=counters.get("collatz_mul3_summary_requests", 0),
        collatz_mul3_summary_cache_hits=counters.get(
            "collatz_mul3_summary_cache_hits", 0
        ),
        collatz_mul3_summary_evaluations=counters.get(
            "collatz_mul3_summary_evaluations", 0
        ),
        joint_interval_composition_requests=counters.get(
            "joint_interval_composition_requests", 0
        ),
        joint_interval_composition_cache_hits=counters.get(
            "joint_interval_composition_cache_hits", 0
        ),
        joint_interval_composition_evaluations=counters.get(
            "joint_interval_composition_evaluations", 0
        ),
        interval_literal_requests=counters.get("interval_literal_requests", 0),
        interval_literal_cache_hits=counters.get("interval_literal_cache_hits", 0),
        interval_literal_evaluations=counters.get("interval_literal_evaluations", 0),
        interval_reflection_requests=counters.get("interval_reflection_requests", 0),
        interval_reflection_cache_hits=counters.get(
            "interval_reflection_cache_hits", 0
        ),
        interval_reflection_identity_hits=counters.get(
            "interval_reflection_identity_hits", 0
        ),
        interval_reflection_evaluations=counters.get(
            "interval_reflection_evaluations", 0
        ),
        interval_effect_intern_hits=counters.get("interval_effect_intern_hits", 0),
        interval_effect_intern_misses=counters.get("interval_effect_intern_misses", 0),
        reverse_summary_lookup_requests=counters.get(
            "reverse_summary_lookup_requests", 0
        ),
        reverse_summary_lookup_hits=counters.get("reverse_summary_lookup_hits", 0),
        reverse_summary_lookup_misses=counters.get("reverse_summary_lookup_misses", 0),
        reverse_summary_reflection_hits=counters.get(
            "reverse_summary_reflection_hits", 0
        ),
        composition_requests=counters.get("composition_requests", 0),
        composition_cache_hits=counters.get("composition_cache_hits", 0),
        composition_evaluations=counters.get("composition_evaluations", 0),
        retained_composition_entries=sum(
            item.composition_entries for item in inventory
        ),
        summary_evaluations=counters.get("summary_evaluations", 0),
        summary_cache_hits=counters.get("summary_cache_hits", 0),
        symbolic_port_queries=counters.get("symbolic_port_queries", 0),
        symbolic_maximum_port_bits=counters.get("symbolic_maximum_port_bits", 0),
        bounded_limb_operations=counters.get("bounded_limb_operations", 0),
        maximum_arithmetic_bits=counters.get("maximum_arithmetic_bits", 0),
        unbounded_arithmetic_observations=counters.get(
            "unbounded_arithmetic_observations", 0
        ),
        endpoint_lowering_requests=counters.get("endpoint_lowering_requests", 0),
        explicitly_lowered_digits=counters.get("explicitly_lowered_digits", 0),
        explicitly_materialized_endpoints=counters.get(
            "explicitly_materialized_endpoints", 0
        ),
    )
    report = replace(
        report,
        temporal_diagnostics=collect_temporal_diagnostics(
            counters,
            entries=snapshot.entries,
            nodes=snapshot.nodes,
            peak_entries=snapshot.peak_entries,
            peak_nodes=snapshot.peak_nodes,
            audit_complete=bool(report.resource_audit_complete),
            accounting_mismatch=(
                report.resource_accounting_mismatch
                if report.resource_audit_complete
                else None
            ),
        ),
    )
    projected = replace_metric(
        report,
        {
            **partition,
            # The quotient owner's retained-node category includes canonical
            # records and their inline bounded arithmetic storage.  Keep that
            # independently observed charge in the node partition; the
            # interface population below counts canonical records only.
            **{name: counters.get(name, 0) for name in QUOTIENT_WORK_COUNTERS},
            **{name: counters.get(name, 0) for name in DIAMOND_WORK_COUNTERS},
            **schema7_work_values(counters),
            # Semantic outcomes are evidence of successful reuse, not
            # executed-work units.
            **{name: counters.get(name, 0) for name in SEMANTIC_OUTCOME_COUNTERS},
            **{
                item.name: counters[item.name]
                for item in fields(report)
                if item.name in SEMANTIC_ADAPTER_WORK_COUNTERS and item.name in counters
            },
            **schema7_inventory_values(inventory),
            "local_interface_nodes": interface_records,
            "causal_geometry_nodes": nodes_for("causal_geometry"),
            "right_reset_certificate_nodes": nodes_for("right_reset_certificate"),
            "finite_cycle_certificate_nodes": nodes_for("finite_cycle_certificate"),
            "cache_events_by_spatial_level": cache_levels,
            "cache_events_by_temporal_span": cache_spans,
            "primitive_behavioral_class_population": sum(
                quotient.left_count + quotient.right_count
                for root in execution_roots
                if type(root) is DiamondKernelArena and root.ledger is ledger
                for quotient in root._behavioral_quotients.values()
            ),
            "completed_result_entries": sum(
                type(value) is CompletedResult for _, value in tile_memo_items
            ),
            "normalized_region_entries": sum(
                type(key) is NormalizedRegionKey
                and type(value) is NormalizedRegionResult
                for key, value in tile_memo_items
            ),
            "boundary_tile_operand_references": len(retained_boundary_views),
            "boundary_tile_unique_live": len(
                {view.tile for view in retained_boundary_views}
            ),
            "boundary_tile_operand_extent_total": sum(
                view.relative_extent for view in retained_boundary_views
            ),
            "boundary_tile_operand_source_offset_total": sum(
                view.source_offset for view in retained_boundary_views
            ),
            "boundary_tile_memo_operand_references": len(boundary_tile_views),
            "boundary_tile_leased_operand_references": len(leased_boundary_views),
            "boundary_tile_leased_operand_unique_live": len(
                {view.tile for view in leased_boundary_views}
            ),
            "boundary_tile_leases": sum(
                root._boundary_lease_count
                for root in execution_roots
                if type(root) is CompletedResultArena and root.ledger is ledger
            ),
            "tile_mirror_relation_entries": sum(
                sum(
                    type(key) is tuple
                    and len(key) == 5
                    and type(key[1]) is int
                    and key == root._mirror_key(key[1])
                    for key in root._keys
                )
                for root in execution_roots
                if type(root) is TileArena and root.ledger is ledger
            ),
            "pinned_completed_roots": sum(
                type(root) is TileApplication
                and root._closed is False
                and type(root._root) is ResultLease
                and root._root._closed is False
                for root in execution_roots
            ),
            "powered_interface_entries": sum(
                type(key) is PoweredInterfaceKey and type(value) is LocalInterfaceID
                for key, value in tile_memo_items
            ),
            "spatial_interface_composition_entries": sum(
                type(key) is SpatialInterfaceKey and type(value) is LocalInterfaceID
                for key, value in tile_memo_items
            ),
            "fused_interface_entries": sum(
                type(key) is FusedInterfaceKey and type(value) is LocalInterfaceID
                for key, value in tile_memo_items
            ),
            **{
                name: sum(
                    item.observed_entries or 0
                    for item in inventory
                    if _role(item.role) == role
                )
                for name, role in DIAMOND_MEMO_ROLES
            },
            "algebraic_instrumentation_complete": int(
                set(ALGEBRAIC_FIELD_WORK_COUNTERS) <= counters.keys()
            ),
            "canonical_parent_identity_entries": sum(
                record.left is not None and record.right is not None
                for root in execution_roots
                if type(root) is TileArena and root.ledger is ledger
                for record in root._nodes.values()
            ),
            "reverse_frobenius_retained_component_nodes": sum(
                retained_action_nodes(record.reverse_frobenius) - 1
                for root in execution_roots
                if type(root) is PrimitiveTileKernelAdapter and root.ledger is ledger
                for record in root._actions.values()
                if record.reverse_frobenius is not None
            ),
            "reverse_port_retained_coefficient_slots": reverse_coefficient_slots,
            "reverse_port_retained_limb_slots": reverse_limb_slots,
            "reverse_sector_retained_slots": reverse_sector_slots,
            "reverse_port_unique_live_function_objects": len(unique_reverse_components),
            "reverse_port_unique_live_coefficient_slots": (
                unique_reverse_coefficient_slots
            ),
            "reverse_port_unique_live_limb_slots": unique_reverse_limb_slots,
            "reverse_sector_unique_live_objects": len(unique_reverse_sectors),
            "reverse_sector_unique_live_slots": unique_reverse_sector_slots,
            "exact_microblock_entries": sum(
                item.observed_entries or 0
                for item in inventory
                if _role(item.role) == "exact_microblock"
            ),
        },
    )
    if (
        ledger.mutation_version != source_version
        or ledger.counters != snapshot.counters
    ):
        raise RuntimeError("execution resources changed during metric projection")
    return projected


def ledger_metric_values(ledger: ResourceLedger) -> dict[str, object]:
    """Keyword fields for dataclasses.replace without flattening typed roots."""
    metrics = collect_ledger_metrics(ledger)
    return {item.name: getattr(metrics, item.name) for item in fields(metrics)}


def ledger_fields_from(metrics: LedgerMetrics) -> dict[str, object]:
    """Forward schema fields through public metric records without recomputing."""
    return {item.name: getattr(metrics, item.name) for item in fields(LedgerMetrics)}


def collect_unindexed_metrics(ledger: ResourceLedger) -> HashLifeProjectionMetrics:
    """Collect a read-only metric snapshot for unindexed terms.

    Call :func:`collect_ledger_metrics` directly when a payload and ownership
    audit is required. Runtime reporting must not run those deep audits.
    """
    report = collect_ledger_metrics(ledger, audit_payloads=False)
    values = ledger_fields_from(report)
    values.update(
        point_queries=report.resource_work_counters.get("temporal_point_requests", 0),
        retained_execution_nodes=report.resource_ledger_nodes,
        compiler_retained_execution_nodes=report.compiler_program_nodes,
        compiler_retained_cache_entries=sum(
            item.entries
            for item in report.resource_inventory
            if _role(item.role)
            in ("compiled_action_program", "compiled_action_interner")
        ),
        retained_cache_entries=report.resource_ledger_entries,
        budgeted_cache_entries=report.resource_ledger_entries,
        retained_cache_accounting_delta=report.resource_accounting_mismatch,
        total_hashlife_retained_entries=report.cache_slots,
        direct_powered_point_queries=report.resource_work_counters.get(
            "direct_powered_point_queries", 0
        ),
    )
    return replace_metric(HashLifeProjectionMetrics(*([0] * 15)), values)
