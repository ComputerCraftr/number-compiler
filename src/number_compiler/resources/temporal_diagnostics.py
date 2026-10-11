"""Schema-eight observations of temporal construction and demand work.

Every nullable count has one meaning: ``None`` means its instrumented owner was
not observed.  A measured zero is an integer zero.  The lanes deliberately do
not add counters with different meanings or use cache hits as construction.
"""

from __future__ import annotations

import sys
from collections.abc import Mapping
from dataclasses import dataclass, replace

from number_compiler.resources.ledger import ResourceLedger

METRICS_SCHEMA_VERSION = 8


@dataclass(frozen=True, slots=True)
class TemporalReuseLane:
    """One owner's requests, reuse and publications in their original units."""

    requests: int | None = None
    attempts: int | None = None
    # Exact and transported hits are producer-classified disjoint outcomes.
    exact_hits: int | None = None
    transported_hits: int | None = None
    local_hits: int | None = None
    process_hits: int | None = None
    applied_hits: int | None = None
    applied_parent_hits: int | None = None
    rejected_fit: int | None = None
    admission_rejections: int | None = None
    key_operand_bits: int | None = None
    # Some older owner lanes have only a literal hit counter. Keep it separate
    # until that producer classifies the returned value.
    unclassified_hits: int | None = None
    misses: int | None = None
    publications: int | None = None
    bypasses: int | None = None
    disabled_bypasses: int | None = None
    policy_bypasses: int | None = None
    capacity_bypasses: int | None = None
    evictions: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalConstruction:
    """Scheduler work; composite application is not source-discovery work."""

    postorder_frames: int | None = None
    primitive_applications: int | None = None
    chronological_compositions: int | None = None
    composite_applications: int | None = None
    demanded_composite_applications: int | None = None
    source_image_publications: int | None = None
    source_image_adapter_registrations: int | None = None
    arithmetic_result_publications: int | None = None
    bootstrap_admission_steps: int | None = None
    reverse_pair_steps: int | None = None
    reverse_pair_sections: int | None = None
    reverse_successor_rows: int | None = None
    reverse_successor_bootstrap_rows: int | None = None
    reverse_successor_spatial_bits: int | None = None
    reverse_successor_pair_symbols: int | None = None
    reverse_successor_event_symbols: int | None = None
    reverse_successor_transport_updates: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalStreamDemand:
    """Output emission measurements, kept distinct from jump construction."""

    requests: int | None = None
    node_visits: int | None = None
    emitted: int | None = None
    boundary_evaluations: int | None = None
    frame_peak: int | None = None
    cancellations: int | None = None
    failures: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalRenderingWork:
    """Complete CLI text rendering, separate from internal native digit streams."""

    requests: int | None = None
    emitted_digits: int | None = None
    failures: int | None = None
    integer_conversion_operand_bits: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalDemand:
    """Term query counts; absent exact counters are not inferred from output."""

    point_requests: int | None = None
    length_requests: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalObservations:
    """Family observation and forbidden replay work, in original units."""

    arithmetic_returns: int | None = None
    arithmetic_result_validation_blocks: int | None = None
    arithmetic_result_validation_reconstructions: int | None = None
    arithmetic_result_validation_operand_bits: int | None = None
    mahler_source_composed_image_reads: int | None = None
    mahler_associated_action_demands: int | None = None
    mahler_root_shell_projections: int | None = None
    mahler_root_shell_operand_bits: int | None = None
    physical_roof_evaluations: int | None = None
    query_observer_reuses: int | None = None
    higher_concrete_operation_evaluations: int | None = None
    higher_action_continuation_requests: int | None = None
    reverse_recursive_pair_width_cache_hits: int | None = None
    reverse_recursive_pair_width_cache_misses: int | None = None
    reverse_recursive_pair_width_publications: int | None = None
    reverse_recursive_pair_width_descents: int | None = None
    reverse_recursive_pair_width_failures: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalGrowthReadout:
    """Demanded homogeneous arithmetic, never endpoint-growth work."""

    work: int | None = None
    operand_bits: int | None = None
    precision_bits: int | None = None
    refinements: int | None = None
    exact_rational_cases: int | None = None
    bounded_exact_ratio_cases: int | None = None
    identity_shortcuts: int | None = None
    log_constant_hits: int | None = None
    cf_requests: int | None = None
    cf_budget_refusals: int | None = None
    order_hits: int | None = None
    budget_refusals: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalFamilyWork:
    """One arithmetic owner's finite source-discovery measurements."""

    counter_prefix: str
    action_requests: int | None
    action_hits: int | None
    action_misses: int | None
    action_publications: int
    macro_requests: int | None
    bounded_base_steps: int | None
    macro_compositions: int | None
    operand_bits: tuple[tuple[str, int], ...]
    transient_leaf_steps: int | None = None
    balanced_effect_compositions: int | None = None
    balanced_macro_compositions: int | None = None
    saturated_support_publications: int | None = None
    composite_cutover_chunks: int | None = None
    composite_cutover_publications: int | None = None
    balanced_effect_memo_lookups: int | None = None
    balanced_effect_memo_hits: int | None = None
    balanced_effect_memo_misses: int | None = None
    balanced_effect_memo_publications: int | None = None
    balanced_effect_memo_evictions: int | None = None
    finite_block_lookups: int | None = None
    finite_block_hits: int | None = None
    finite_block_misses: int | None = None
    finite_block_publications: int | None = None
    finite_block_evictions: int | None = None
    finite_block_cold_atoms: int | None = None
    finite_block_cold_steps: int | None = None
    run_actions: int | None = None
    zero_run_pumps: int | None = None
    one_run_pumps: int | None = None
    cycle_pumps: int | None = None
    represented_cycle_repetitions: int | None = None
    run_contraction_publications: int | None = None
    run_routes: int | None = None
    balanced_routes: int | None = None
    punctured_event_actions: int | None = None
    punctured_event_symbols: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalCommaWork:
    """Guarded comma construction; represented cycles are not executed work."""

    operations: int | None = None
    binary_compositions: int | None = None
    transfer_constructions: int | None = None
    transfer_phase_terms: int | None = None
    cycle_rule_evaluations: int | None = None
    child_candidate_checks: int | None = None
    seam_predicate_check_bound: int | None = None
    operand_bits: int | None = None
    represented_phase_cycles: int | None = None
    powered_image_applications: int | None = None
    represented_transitions: int | None = None
    evaluated_transitions: int | None = None
    seam_steps: int | None = None
    relative_guard_checks: int | None = None
    relative_cycle_rebindings: int | None = None
    boundary_template_hits: int | None = None
    boundary_template_misses: int | None = None
    boundary_template_publications: int | None = None
    boundary_template_retained_nodes: int | None = None
    boundary_seal_checks: int | None = None
    boundary_explicit_audit_component_checks: int | None = None
    boundary_explicit_audit_operand_bits: int | None = None
    boundary_seal_retained_slots: int | None = None
    boundary_seal_retained_integer_bits: int | None = None
    boundary_prefix_applications: int | None = None
    boundary_represented_transitions: int | None = None
    stream_requests: int | None = None
    stream_emitted_digits: int | None = None
    stream_workspace_peak_slots: int | None = None
    stream_workspace_peak_integer_bits: int | None = None
    certificate_operations: int | None = None
    certificate_sector_entries: int | None = None
    certificate_boundary_classifications: int | None = None
    certificate_candidate_digit_trials: int | None = None
    certificate_operand_bits: int | None = None
    certificate_read_bytes: int | None = None
    certificate_uncompressed_bytes: int | None = None
    certificate_frontier_peak: int | None = None
    certificate_local_hits: int | None = None
    certificate_cache_hits: int | None = None
    certificate_cache_misses: int | None = None
    certificate_cache_bypasses: int | None = None
    certificate_cache_publications: int | None = None
    budget_refusals: int | None = None
    certificate_budget_refusals: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalResources:
    """Whole-ledger retention; these counts are never attributed to one lane."""

    entries: int | None = None
    nodes: int | None = None
    peak_entries: int | None = None
    peak_nodes: int | None = None
    audit_complete: bool | None = None
    accounting_mismatch: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalReportingWork:
    """Measured reporting traversal, separate from computational work."""

    captured_counter_items: int | None = None
    captured_mapping_bytes: int | None = None
    projected_counter_items: int | None = None
    inspected_inventory_rows: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalMacrocellWork:
    """Semantic interning and occurrence application are separate reuse lanes.

    ``max_level`` is log2 of represented family transitions (D8 is level 3),
    never an archive-specific level relative to its bootstrap size. A semantic
    hit alone makes no claim that occurrence construction was avoided.
    """

    family: str
    index_unit: str
    cache_scope: str
    semantic: TemporalReuseLane
    occurrence: TemporalReuseLane
    source_action: TemporalReuseLane = TemporalReuseLane()
    outer_observer: TemporalReuseLane = TemporalReuseLane()
    width_projection: TemporalReuseLane = TemporalReuseLane()
    outer_observer_scope: str | None = None
    merges: int | None = None
    max_level: int | None = None
    primitive_steps: int | None = None
    spatial_leaf_visits: int | None = None
    operand_bits: int | None = None
    key_operand_bits: int | None = None
    cold_child_discoveries: int | None = None
    coefficient_compositions: int | None = None
    occurrence_frontier_joins: int | None = None
    gain_local_hits: int | None = None
    gain_process_hits: int | None = None
    gain_key_operand_bits: int | None = None
    gain_construction_operand_bits: int | None = None
    gain_validation_operand_bits: int | None = None
    gain_bypasses: int | None = None
    capacity_bypasses: int | None = None
    output_region_visits: int | None = None
    emitted_digits: int | None = None
    failed_work: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalAffineWidth:
    """Charged exact width comparisons, distinct from growth or emitted digits."""

    requests: int | None = None
    operand_bits: int | None = None
    interval_checks: int | None = None
    refinements: int | None = None
    exact_boundaries: int | None = None
    failures: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalExecutionDiagnostics:
    """Compact schema-eight view beside the preserved raw work counters."""

    schema_version: int = METRICS_SCHEMA_VERSION
    action: TemporalReuseLane = TemporalReuseLane()
    application: TemporalReuseLane = TemporalReuseLane()
    projection: TemporalReuseLane = TemporalReuseLane()
    construction: TemporalConstruction = TemporalConstruction()
    demand: TemporalDemand = TemporalDemand()
    stream: TemporalStreamDemand = TemporalStreamDemand()
    observations: TemporalObservations = TemporalObservations()
    growth_readout: TemporalGrowthReadout = TemporalGrowthReadout()
    affine_width: TemporalAffineWidth = TemporalAffineWidth()
    family_work: tuple[TemporalFamilyWork, ...] = ()
    macrocells: tuple[TemporalMacrocellWork, ...] = ()
    comma: TemporalCommaWork = TemporalCommaWork()
    resources: TemporalResources = TemporalResources()
    reporting: TemporalReportingWork = TemporalReportingWork()
    rendering: TemporalRenderingWork = TemporalRenderingWork()


_ACTION_PREFIXES = (
    "antihydra_arithmetic",
    "collatz_physical",
    "dyadic_return",
    "comma",
)


def _count(counters: Mapping[str, int], key: str) -> int | None:
    value = counters.get(key)
    if value is None:
        return None
    if type(value) is not int or value < 0:
        raise ValueError(f"temporal counter {key} is not a nonnegative integer")
    return value


def _macrocell_reuse(
    counters: Mapping[str, int], prefix: str, kind: str
) -> TemporalReuseLane:
    bypass_counts = {
        reason: _count(counters, f"{prefix}{kind}_{suffix}")
        for reason, suffix in (
            ("capacity", "bypasses"),
            ("disabled", "disabled_bypasses"),
            ("policy", "policy_bypasses"),
        )
    }
    observed_bypasses = [value for value in bypass_counts.values() if value is not None]
    lane = TemporalReuseLane(
        requests=_count(counters, f"{prefix}{kind}_lookups"),
        exact_hits=_count(counters, f"{prefix}{kind}_exact_hits"),
        transported_hits=_count(counters, f"{prefix}{kind}_transported_hits"),
        local_hits=_count(counters, f"{prefix}{kind}_local_hits"),
        process_hits=_count(counters, f"{prefix}{kind}_process_hits"),
        applied_hits=_count(counters, f"{prefix}{kind}_applied_hits"),
        applied_parent_hits=_count(counters, f"{prefix}{kind}_applied_parent_hits"),
        rejected_fit=_count(counters, f"{prefix}{kind}_rejected_fit"),
        admission_rejections=_count(counters, f"{prefix}{kind}_admission_rejections"),
        key_operand_bits=_count(counters, f"{prefix}{kind}_key_operand_bits"),
        unclassified_hits=_count(counters, f"{prefix}{kind}_hits"),
        misses=_count(counters, f"{prefix}{kind}_misses"),
        publications=_count(counters, f"{prefix}{kind}_publications"),
        bypasses=sum(observed_bypasses) if observed_bypasses else None,
        capacity_bypasses=(
            bypass_counts["capacity"]
            if kind in ("action", "occurrence", "source_action")
            else None
        ),
        disabled_bypasses=bypass_counts["disabled"],
        policy_bypasses=bypass_counts["policy"],
        evictions=_count(counters, f"{prefix}{kind}_evictions"),
    )
    exact, transported = lane.exact_hits, lane.transported_hits
    if exact is not None and transported is not None:
        hits = exact + transported
        if lane.requests is not None and hits > lane.requests:
            raise ValueError(f"{prefix}{kind} classified more hits than lookups")
        if (
            lane.misses is not None
            and lane.requests is not None
            and hits + lane.misses + (lane.admission_rejections or 0) != lane.requests
        ):
            raise ValueError(
                f"{prefix}{kind} hits, misses and rejections do not partition lookups"
            )
        located_hits = (lane.local_hits, lane.process_hits)
        if (
            all(value is not None for value in located_hits)
            and sum(value for value in located_hits if value is not None) != hits
        ):
            raise ValueError(f"{prefix}{kind} cache locations do not partition hits")
        if lane.applied_hits is not None and lane.applied_hits > hits:
            raise ValueError(f"{prefix}{kind} applied more hits than it retrieved")
        if lane.rejected_fit is not None and (
            lane.rejected_fit + (lane.applied_hits or 0) > hits
        ):
            raise ValueError(
                f"{prefix}{kind} fit rejections and applications exceed retrievals"
            )
        if (
            lane.applied_parent_hits is not None
            and lane.applied_hits is not None
            and lane.applied_parent_hits > lane.applied_hits
        ):
            raise ValueError(f"{prefix}{kind} applied-parent hits exceed applied hits")
    return lane


def _stream_demand(counters: Mapping[str, int]) -> TemporalStreamDemand:
    # Final digit consumers take precedence over the underlying pair-symbol
    # traversal. Counting both would double charge emissions and omit the
    # distinction between a pair cell and a final terminal-carry digit.
    prefixes = [
        prefix
        for prefix in (
            "reverse_output_stream_",
            "collatz_output_stream_",
            "antihydra_output_stream_",
            "comma_stream_",
        )
        if prefix + "requests" in counters
    ]
    if not prefixes:
        prefixes = ["recursive_output_stream_"]
    values: dict[str, int | None] = {}
    for name in ("requests", "emitted_digits", "cancellations", "failures"):
        counts = [_count(counters, prefix + name) for prefix in prefixes]
        values[name] = (
            sum(value for value in counts if value is not None)
            if all(value is not None for value in counts)
            else None
        )
    return TemporalStreamDemand(
        requests=values["requests"],
        emitted=values["emitted_digits"],
        cancellations=values["cancellations"],
        failures=values["failures"],
        node_visits=_count(counters, "recursive_output_stream_node_visits"),
        boundary_evaluations=_count(
            counters, "recursive_output_stream_boundary_evaluations"
        ),
        frame_peak=_count(counters, "recursive_output_stream_frame_peak"),
    )


def _capacity_bypasses(counters: Mapping[str, int], family: str) -> int | None:
    """Sum refused publications from the instrumented stores, once per attempt."""
    if family == "comma":
        return _count(counters, "comma_hashlife_capacity_bypasses")
    kinds = (
        ("action", "source_action")
        if family == "mahler"
        else ("occurrence", "source_action")
        if family == "antihydra"
        else ("occurrence",)
    )
    measured = [
        value
        for kind in kinds
        if (value := _count(counters, f"{family}_hashlife_{kind}_bypasses")) is not None
    ]
    return sum(measured) if measured else None


def _macrocell_work(counters: Mapping[str, int]) -> tuple[TemporalMacrocellWork, ...]:
    rows = []
    for family in ("reverse", "collatz", "antihydra", "mahler", "comma"):
        prefix = f"{family}_hashlife_"
        if not any(name.startswith(prefix) for name in counters):
            continue
        rows.append(
            TemporalMacrocellWork(
                family=family,
                index_unit="normalized_symbol"
                if family == "collatz"
                else "reverse_add_iteration"
                if family == "reverse"
                else "oeis_transition"
                if family == "comma"
                else "macro_return",
                cache_scope="guarded_interior_cycle_action"
                if family == "comma"
                else "source_occurrence_associated_action"
                if family == "mahler"
                and counters.get(f"{prefix}source_action_active", 0)
                else "complete_associated_action"
                if family == "mahler"
                else "source_cylinder",
                semantic=_macrocell_reuse(counters, prefix, "semantic"),
                occurrence=(
                    TemporalReuseLane()
                    if family == "mahler"
                    else _macrocell_reuse(counters, prefix, "occurrence")
                ),
                source_action=(
                    _macrocell_reuse(counters, prefix, "source_action")
                    if family in ("mahler", "antihydra")
                    else TemporalReuseLane()
                ),
                outer_observer=(
                    _macrocell_reuse(counters, prefix, "action")
                    if family == "mahler"
                    else TemporalReuseLane()
                ),
                outer_observer_scope=(
                    "process_complete_associated_action" if family == "mahler" else None
                ),
                width_projection=_macrocell_reuse(counters, prefix, "width_spine"),
                merges=_count(counters, f"{prefix}merges"),
                max_level=_count(counters, f"{prefix}max_level"),
                primitive_steps=_count(counters, f"{prefix}primitive_steps"),
                spatial_leaf_visits=_count(counters, f"{prefix}spatial_leaf_visits"),
                operand_bits=_count(counters, f"{prefix}operand_bits"),
                key_operand_bits=_count(counters, f"{prefix}key_operand_bits"),
                cold_child_discoveries=_count(
                    counters, f"{prefix}cold_child_discoveries"
                ),
                coefficient_compositions=_count(
                    counters, f"{prefix}coefficient_compositions"
                ),
                occurrence_frontier_joins=_count(
                    counters, f"{prefix}occurrence_frontier_joins"
                ),
                gain_local_hits=_count(counters, f"{prefix}gain_local_hits"),
                gain_process_hits=_count(counters, f"{prefix}gain_process_hits"),
                gain_key_operand_bits=_count(
                    counters, f"{prefix}gain_key_operand_bits"
                ),
                gain_construction_operand_bits=_count(
                    counters, f"{prefix}gain_construction_operand_bits"
                ),
                gain_validation_operand_bits=_count(
                    counters, f"{prefix}gain_validation_operand_bits"
                ),
                gain_bypasses=_count(counters, f"{prefix}gain_bypasses"),
                capacity_bypasses=_capacity_bypasses(counters, family),
                output_region_visits=_count(counters, f"{prefix}output_region_visits"),
                emitted_digits=_count(counters, f"{prefix}emitted_digits"),
                failed_work=_count(counters, f"{prefix}failed_work"),
            )
        )
    return tuple(rows)


def collect_temporal_diagnostics(
    counters: Mapping[str, int],
    *,
    entries: int,
    nodes: int,
    peak_entries: int,
    peak_nodes: int,
    audit_complete: bool,
    accounting_mismatch: int | None,
) -> TemporalExecutionDiagnostics:
    """Project exactly one immutable ledger snapshot without evaluating actions."""
    operand_bits: dict[str, list[tuple[str, int]]] = {
        prefix: [] for prefix in _ACTION_PREFIXES
    }
    for name, value in counters.items():
        if type(value) is not int or value < 0:
            raise ValueError("temporal diagnostics require exact nonnegative counters")
        if name.endswith("operand_bits") or name == "comma_operand_bit_work":
            for prefix in _ACTION_PREFIXES:
                if name.startswith(f"{prefix}_"):
                    operand_bits[prefix].append((name, value))
                    break
    if any(
        type(value) is not int or value < 0
        for value in (entries, nodes, peak_entries, peak_nodes)
    ):
        raise ValueError("temporal diagnostics require exact resource counts")
    if accounting_mismatch is not None and (
        type(accounting_mismatch) is not int or accounting_mismatch < 0
    ):
        raise ValueError("temporal diagnostics require exact accounting counts")
    if type(audit_complete) is not bool:
        raise TypeError("temporal audit status must be Boolean")
    if audit_complete and accounting_mismatch is None:
        raise ValueError("completed audit requires an accounting measurement")

    # Source-image publication includes origins and applications.  They are
    # disjoint, so subtraction is exact; projection publication has its own
    # owner and is never included here.
    source_publications = _count(counters, "source_image_publications")
    origin_publications = _count(counters, "source_image_origin_publications")
    application_publications = _count(counters, "source_image_application_publications")
    if (
        source_publications is not None
        and origin_publications is not None
        and application_publications is not None
        and application_publications + origin_publications != source_publications
    ):
        raise ValueError("source-image publication categories do not reconcile")

    families: list[TemporalFamilyWork] = []
    for prefix in _ACTION_PREFIXES:
        enabled = f"{prefix}_action_publications" in counters
        if not enabled:
            continue

        family_bits = tuple(sorted(operand_bits[prefix]))
        families.append(
            TemporalFamilyWork(
                prefix,
                _count(counters, f"{prefix}_action_requests"),
                _count(counters, f"{prefix}_action_hits"),
                _count(counters, f"{prefix}_action_misses"),
                counters[f"{prefix}_action_publications"],
                _count(counters, f"{prefix}_macro_requests"),
                _count(counters, f"{prefix}_macro_bounded_base_steps"),
                _count(counters, f"{prefix}_macro_compositions"),
                family_bits,
                _count(counters, f"{prefix}_transient_leaf_steps"),
                _count(counters, f"{prefix}_balanced_effect_compositions"),
                _count(counters, f"{prefix}_balanced_macro_compositions"),
                _count(counters, f"{prefix}_saturated_support_publications"),
                _count(counters, f"{prefix}_composite_cutover_chunks"),
                _count(counters, f"{prefix}_composite_cutover_publications"),
                _count(counters, f"{prefix}_balanced_effect_memo_lookups"),
                _count(counters, f"{prefix}_balanced_effect_memo_hits"),
                _count(counters, f"{prefix}_balanced_effect_memo_misses"),
                _count(counters, f"{prefix}_balanced_effect_memo_publications"),
                _count(counters, f"{prefix}_balanced_effect_memo_evictions"),
                _count(counters, f"{prefix}_finite_block_lookups"),
                _count(counters, f"{prefix}_finite_block_hits"),
                _count(counters, f"{prefix}_finite_block_misses"),
                _count(counters, f"{prefix}_finite_block_publications"),
                _count(counters, f"{prefix}_finite_block_evictions"),
                _count(counters, f"{prefix}_finite_block_cold_atoms"),
                _count(counters, f"{prefix}_finite_block_cold_steps"),
                _count(counters, f"{prefix}_temporal_run_actions"),
                _count(counters, f"{prefix}_temporal_zero_run_pumps"),
                _count(counters, f"{prefix}_temporal_one_run_pumps"),
                _count(counters, f"{prefix}_temporal_cycle_pump_requests"),
                _count(counters, f"{prefix}_temporal_cycle_pump_repetitions"),
                _count(counters, f"{prefix}_run_contraction_publications"),
                _count(counters, f"{prefix}_temporal_run_routes"),
                _count(counters, f"{prefix}_temporal_balanced_routes"),
                _count(counters, f"{prefix}_temporal_punctured_event_actions"),
                _count(counters, f"{prefix}_temporal_punctured_event_symbols"),
            )
        )

    sole_family = families[0] if len(families) == 1 else None
    # Until the executable bootstrap checker emits this count, its scope is
    # unavailable.  Existing bounded-base steps do not imply admissibility.
    bootstrap = counters.get("temporal_bootstrap_admission_steps")
    if bootstrap is not None and (type(bootstrap) is not int or bootstrap < 0):
        raise ValueError("temporal bootstrap scope is invalid")
    return TemporalExecutionDiagnostics(
        action=TemporalReuseLane(
            requests=None if sole_family is None else sole_family.action_requests,
            exact_hits=None if sole_family is None else sole_family.action_hits,
            misses=None if sole_family is None else sole_family.action_misses,
            publications=(
                None if sole_family is None else sole_family.action_publications
            ),
        ),
        application=TemporalReuseLane(
            requests=_count(counters, "source_image_application_requests"),
            attempts=_count(counters, "source_image_application_attempts"),
            exact_hits=_count(counters, "source_image_application_hits"),
            transported_hits=_count(counters, "source_image_relative_transfer_hits"),
            misses=_count(counters, "source_image_application_misses"),
            publications=application_publications,
        ),
        projection=TemporalReuseLane(
            requests=_count(counters, "source_image_projection_requests"),
            exact_hits=_count(counters, "source_image_projection_hits"),
            misses=_count(counters, "source_image_projection_misses"),
            publications=_count(counters, "source_image_projection_publications"),
        ),
        construction=TemporalConstruction(
            postorder_frames=_count(counters, "source_image_postorder_frames"),
            primitive_applications=_count(
                counters, "source_image_primitive_applications"
            ),
            chronological_compositions=_count(
                counters, "source_image_chronological_compositions"
            ),
            composite_applications=_count(
                counters, "source_image_composite_applications"
            ),
            demanded_composite_applications=_count(
                counters, "source_image_demanded_composite_applications"
            ),
            source_image_publications=source_publications,
            source_image_adapter_registrations=_count(
                counters, "source_image_adapter_registrations"
            ),
            arithmetic_result_publications=_count(
                counters, "arithmetic_result_publications"
            ),
            bootstrap_admission_steps=bootstrap,
            reverse_pair_steps=_count(
                counters, "reverse_q19_primitive_pair_applications"
            ),
            reverse_pair_sections=_count(
                counters, "reverse_q19_pair_output_nodes_visited"
            ),
            reverse_successor_rows=_count(counters, "reverse_successor_tape_rows"),
            reverse_successor_bootstrap_rows=_count(
                counters, "reverse_successor_tape_bootstrap_rows"
            ),
            reverse_successor_spatial_bits=_count(
                counters, "reverse_successor_tape_spatial_bits"
            ),
            reverse_successor_pair_symbols=_count(
                counters, "reverse_successor_tape_pair_operand_symbols"
            ),
            reverse_successor_event_symbols=_count(
                counters, "reverse_successor_tape_event_symbols"
            ),
            reverse_successor_transport_updates=_count(
                counters, "reverse_successor_tape_reconstruction_coefficient_updates"
            ),
        ),
        demand=TemporalDemand(
            point_requests=_count(counters, "temporal_point_requests"),
            length_requests=_count(counters, "temporal_length_requests"),
        ),
        stream=_stream_demand(counters),
        rendering=TemporalRenderingWork(
            requests=_count(counters, "cli_render_requests"),
            emitted_digits=_count(counters, "cli_render_emitted_digits"),
            failures=_count(counters, "cli_render_failures"),
            integer_conversion_operand_bits=_count(
                counters, "cli_render_integer_conversion_operand_bits"
            ),
        ),
        affine_width=TemporalAffineWidth(
            requests=_count(counters, "affine_width_requests"),
            operand_bits=_count(counters, "affine_width_operand_bits"),
            interval_checks=_count(counters, "affine_width_interval_checks"),
            refinements=_count(counters, "affine_width_refinements"),
            exact_boundaries=_count(counters, "affine_width_exact_boundaries"),
            failures=_count(counters, "affine_width_failures"),
        ),
        growth_readout=TemporalGrowthReadout(
            work=_count(counters, "growth_arithmetic_work"),
            operand_bits=_count(counters, "growth_arithmetic_operand_bits"),
            precision_bits=_count(counters, "growth_arithmetic_precision_bits"),
            refinements=_count(counters, "growth_order_refinements"),
            exact_rational_cases=_count(counters, "growth_order_exact_rational_cases"),
            bounded_exact_ratio_cases=_count(
                counters, "growth_order_bounded_exact_ratio_cases"
            ),
            identity_shortcuts=_count(counters, "growth_order_identity_shortcuts"),
            log_constant_hits=_count(counters, "growth_log_constant_cache_hits"),
            cf_requests=_count(counters, "growth_cf_key_lookups"),
            cf_budget_refusals=_count(counters, "growth_cf_budget_refusals"),
            order_hits=_count(counters, "growth_order_cache_hits"),
            budget_refusals=_count(counters, "growth_arithmetic_budget_refusals"),
        ),
        observations=TemporalObservations(
            arithmetic_returns=_count(counters, "arithmetic_returns"),
            arithmetic_result_validation_blocks=_count(
                counters, "arithmetic_result_validation_blocks"
            ),
            arithmetic_result_validation_reconstructions=_count(
                counters, "arithmetic_result_validation_reconstructions"
            ),
            arithmetic_result_validation_operand_bits=_count(
                counters, "arithmetic_result_validation_operand_bits"
            ),
            mahler_source_composed_image_reads=_count(
                counters, "mahler_source_composed_image_reads"
            ),
            mahler_associated_action_demands=_count(
                counters, "mahler_associated_action_demands"
            ),
            mahler_root_shell_projections=_count(
                counters, "mahler_root_shell_projections"
            ),
            mahler_root_shell_operand_bits=_count(
                counters, "mahler_root_shell_operand_bits"
            ),
            physical_roof_evaluations=_count(counters, "physical_roof_evaluations"),
            query_observer_reuses=_count(counters, "query_observer_reuses"),
            higher_concrete_operation_evaluations=_count(
                counters, "higher_concrete_operation_evaluations"
            ),
            higher_action_continuation_requests=_count(
                counters, "higher_action_continuation_requests"
            ),
            reverse_recursive_pair_width_cache_hits=_count(
                counters, "reverse_recursive_pair_width_cache_hits"
            ),
            reverse_recursive_pair_width_cache_misses=_count(
                counters, "reverse_recursive_pair_width_cache_misses"
            ),
            reverse_recursive_pair_width_publications=_count(
                counters, "reverse_recursive_pair_width_publications"
            ),
            reverse_recursive_pair_width_descents=_count(
                counters, "reverse_recursive_pair_width_descents"
            ),
            reverse_recursive_pair_width_failures=_count(
                counters, "reverse_recursive_pair_width_failures"
            ),
        ),
        family_work=tuple(families),
        comma=TemporalCommaWork(
            operations=_count(counters, "comma_work"),
            binary_compositions=_count(counters, "comma_binary_composition_work"),
            transfer_constructions=_count(counters, "comma_transfer_constructions"),
            transfer_phase_terms=_count(counters, "comma_transfer_phase_terms"),
            cycle_rule_evaluations=_count(counters, "comma_cycle_rule_evaluations"),
            child_candidate_checks=_count(counters, "comma_child_candidate_checks"),
            seam_predicate_check_bound=_count(counters, "comma_seam_predicate_checks"),
            operand_bits=_count(counters, "comma_operand_bit_work"),
            represented_phase_cycles=_count(counters, "comma_phase_cycles"),
            powered_image_applications=_count(
                counters, "comma_powered_image_applications"
            ),
            represented_transitions=_count(counters, "comma_represented_transitions"),
            evaluated_transitions=_count(counters, "comma_evaluated_transitions"),
            seam_steps=_count(counters, "comma_scalar_seam_steps"),
            relative_guard_checks=_count(counters, "comma_relative_guard_checks"),
            relative_cycle_rebindings=_count(
                counters, "comma_relative_cycle_rebindings"
            ),
            boundary_template_hits=_count(counters, "comma_boundary_template_hits"),
            boundary_template_misses=_count(counters, "comma_boundary_template_misses"),
            boundary_template_publications=_count(
                counters, "comma_boundary_template_publications"
            ),
            boundary_template_retained_nodes=_count(
                counters, "comma_boundary_template_retained_nodes"
            ),
            boundary_seal_checks=_count(counters, "comma_boundary_seal_checks"),
            boundary_explicit_audit_component_checks=_count(
                counters, "comma_boundary_explicit_audit_component_checks"
            ),
            boundary_explicit_audit_operand_bits=_count(
                counters, "comma_boundary_explicit_audit_operand_bits"
            ),
            boundary_seal_retained_slots=_count(
                counters, "comma_boundary_seal_retained_slots"
            ),
            boundary_seal_retained_integer_bits=_count(
                counters, "comma_boundary_seal_retained_integer_bits"
            ),
            boundary_prefix_applications=_count(
                counters, "comma_boundary_prefix_applications"
            ),
            boundary_represented_transitions=_count(
                counters, "comma_boundary_represented_transitions"
            ),
            stream_requests=_count(counters, "comma_stream_requests"),
            stream_emitted_digits=_count(counters, "comma_stream_emitted_digits"),
            stream_workspace_peak_slots=_count(
                counters, "comma_stream_workspace_peak_slots"
            ),
            stream_workspace_peak_integer_bits=_count(
                counters, "comma_stream_workspace_peak_integer_bits"
            ),
            certificate_operations=_count(counters, "comma_certificate_work"),
            certificate_sector_entries=_count(
                counters, "comma_certificate_sector_entries"
            ),
            certificate_boundary_classifications=_count(
                counters, "comma_certificate_boundary_classifications"
            ),
            certificate_candidate_digit_trials=_count(
                counters, "comma_certificate_candidate_digit_trials"
            ),
            certificate_operand_bits=_count(
                counters, "comma_certificate_operand_bit_work"
            ),
            certificate_read_bytes=_count(counters, "comma_certificate_read_bytes"),
            certificate_uncompressed_bytes=_count(
                counters, "comma_certificate_uncompressed_bytes"
            ),
            certificate_frontier_peak=_count(
                counters, "comma_certificate_frontier_peak"
            ),
            certificate_local_hits=_count(counters, "comma_certificate_local_hits"),
            certificate_cache_hits=_count(counters, "comma_certificate_cache_hits"),
            certificate_cache_misses=_count(counters, "comma_certificate_cache_misses"),
            certificate_cache_bypasses=_count(
                counters, "comma_certificate_cache_bypasses"
            ),
            certificate_cache_publications=_count(
                counters, "comma_certificate_cache_publications"
            ),
            budget_refusals=_count(counters, "comma_budget_refusals"),
            certificate_budget_refusals=_count(
                counters, "comma_certificate_budget_refusals"
            ),
        ),
        macrocells=_macrocell_work(counters),
        resources=TemporalResources(
            entries,
            nodes,
            peak_entries,
            peak_nodes,
            audit_complete,
            accounting_mismatch,
        ),
        reporting=TemporalReportingWork(projected_counter_items=len(counters)),
    )


def collect_temporal_diagnostics_snapshot(
    ledger: ResourceLedger,
) -> TemporalExecutionDiagnostics:
    """Capture CLI diagnostics without a semantic audit or endpoint demand.

    The term/query owner is serial. Copying the scalar work counters detaches
    them from later demands; retained resources come from the ledger's scalar
    totals. Inventory callbacks and their potentially expensive payload walks
    are intentionally reserved for the explicit full-audit collector.
    """
    if type(ledger) is not ResourceLedger:
        raise TypeError("temporal diagnostics require one resource ledger")
    counters = dict(ledger.counters)
    report = collect_temporal_diagnostics(
        counters,
        entries=ledger.entries,
        nodes=ledger.nodes,
        peak_entries=ledger.peak_entries,
        peak_nodes=ledger.peak_nodes,
        audit_complete=False,
        accounting_mismatch=None,
    )
    return replace(
        report,
        reporting=TemporalReportingWork(
            captured_counter_items=len(counters),
            captured_mapping_bytes=sys.getsizeof(counters),
            projected_counter_items=len(counters),
            inspected_inventory_rows=0,
        ),
    )
