"""Schema-eight observations of temporal construction and demand work.

Every nullable count has one meaning: ``None`` means its instrumented owner was
not observed.  A measured zero is an integer zero.  The lanes deliberately do
not add counters with different meanings or use cache hits as construction.
"""

from __future__ import annotations

import sys
from collections.abc import Mapping
from dataclasses import replace

from number_compiler.resources.cellular_diagnostics import (
    collect_cellular_work,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.resources.metric_keys import api as _api_keys
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.resources.metric_keys import double_reverse as _double_reverse_keys
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.reuse_diagnostics import (
    TemporalReuseLane,
    collect_complete_action_reuse,
)
from number_compiler.resources.temporal_diagnostic_records import (
    METRICS_SCHEMA_VERSION,
    TemporalAffineWidth,
    TemporalCommaWork,
    TemporalConstruction,
    TemporalDemand,
    TemporalExecutionDiagnostics,
    TemporalFamilyWork,
    TemporalGrowthReadout,
    TemporalMacrocellWork,
    TemporalObservations,
    TemporalRenderingWork,
    TemporalReportingWork,
    TemporalResources,
    TemporalStreamDemand,
)

_ACTION_PREFIXES = (
    "antihydra_arithmetic",
    "collatz_physical",
    "dyadic_return",
    "comma",
)


def _named_work(
    counters: Mapping[str, int], prefix: str
) -> tuple[tuple[str, int], ...] | None:
    """Snapshot an instrumented owner without inventing measurements."""
    return (
        tuple(
            sorted(
                (name.removeprefix(prefix), value)
                for name, value in counters.items()
                if name.startswith(prefix)
            )
        )
        or None
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
            if kind in ("action", "occurrence", "source_action", "joint")
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
            "double_reverse_output_stream_",
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
        node_visits=_count(counters, _shared_keys.RECURSIVE_OUTPUT_STREAM_NODE_VISITS),
        boundary_evaluations=_count(
            counters,
            _execution_keys.RECURSIVE_OUTPUT_STREAM_BOUNDARY_EVALUATIONS,
        ),
        frame_peak=_count(counters, _execution_keys.RECURSIVE_OUTPUT_STREAM_FRAME_PEAK),
    )


def _capacity_bypasses(counters: Mapping[str, int], family: str) -> int | None:
    """Sum refused publications from the instrumented stores, once per attempt."""
    if family == "comma":
        return _count(counters, _comma_keys.COMMA_HASHLIFE_CAPACITY_BYPASSES)
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
                joint_action=_macrocell_reuse(counters, prefix, "joint"),
                mixed_action=collect_complete_action_reuse(counters, prefix + "mixed_"),
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
        if name.endswith("operand_bits") or name == _comma_keys.COMMA_OPERAND_BIT_WORK:
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
    source_publications = _count(counters, _execution_keys.SOURCE_IMAGE_PUBLICATIONS)
    origin_publications = _count(
        counters, _execution_keys.SOURCE_IMAGE_ORIGIN_PUBLICATIONS
    )
    application_publications = _count(
        counters, _execution_keys.SOURCE_IMAGE_APPLICATION_PUBLICATIONS
    )
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
                *(
                    _count(counters, f"collatz_boundary_template_{field}")
                    if prefix == "collatz_physical"
                    else None
                    for field in (
                        "lookups",
                        "hits",
                        "misses",
                        "publications",
                        "bypasses",
                    )
                ),
                *(
                    _count(counters, f"collatz_boundary_prefix_{field}")
                    if prefix == "collatz_physical"
                    else None
                    for field in (
                        "macro_requests",
                        "root_candidates",
                        "global_root_candidates",
                        "slice_candidates",
                        "action_operand_bits",
                        "source_operand_bits",
                        "publications",
                        "budget_bypasses",
                    )
                ),
                root_checkpoint_work=tuple(
                    sorted(
                        (name.removeprefix("collatz_temporal_root_checkpoint_"), value)
                        for name, value in counters.items()
                        if prefix == "collatz_physical"
                        and name.startswith("collatz_temporal_root_checkpoint_")
                    )
                ),
                border_return_work=tuple(
                    sorted(
                        (name.removeprefix(f"{prefix}_border_return_"), value)
                        for name, value in counters.items()
                        if name.startswith(f"{prefix}_border_return_")
                    )
                ),
                odd_macro_work=_named_work(counters, f"{prefix}_temporal_odd_macro_"),
                mixed_clock_work=_named_work(
                    counters, f"{prefix}_temporal_mixed_clock_macro_"
                ),
                conditional_scheduler_work=(
                    _named_work(counters, "collatz_conditional_scheduler_")
                    if prefix == "collatz_physical"
                    else None
                ),
            )
        )

    sole_family = families[0] if len(families) == 1 else None
    # Until the executable bootstrap checker emits this count, its scope is
    # unavailable.  Existing bounded-base steps do not imply admissibility.
    bootstrap = counters.get("temporal_bootstrap_admission_steps")
    if bootstrap is not None and (type(bootstrap) is not int or bootstrap < 0):
        raise ValueError("temporal bootstrap scope is invalid")
    return TemporalExecutionDiagnostics(
        cellular=collect_cellular_work(counters),
        action=TemporalReuseLane(
            requests=None if sole_family is None else sole_family.action_requests,
            exact_hits=None if sole_family is None else sole_family.action_hits,
            misses=None if sole_family is None else sole_family.action_misses,
            publications=(
                None if sole_family is None else sole_family.action_publications
            ),
        ),
        application=TemporalReuseLane(
            requests=_count(
                counters, _execution_keys.SOURCE_IMAGE_APPLICATION_REQUESTS
            ),
            attempts=_count(
                counters, _execution_keys.SOURCE_IMAGE_APPLICATION_ATTEMPTS
            ),
            exact_hits=_count(counters, _execution_keys.SOURCE_IMAGE_APPLICATION_HITS),
            transported_hits=_count(
                counters,
                _execution_keys.SOURCE_IMAGE_RELATIVE_TRANSFER_HITS,
            ),
            misses=_count(counters, _execution_keys.SOURCE_IMAGE_APPLICATION_MISSES),
            publications=application_publications,
        ),
        projection=TemporalReuseLane(
            requests=_count(counters, _execution_keys.SOURCE_IMAGE_PROJECTION_REQUESTS),
            exact_hits=_count(counters, _execution_keys.SOURCE_IMAGE_PROJECTION_HITS),
            misses=_count(counters, _execution_keys.SOURCE_IMAGE_PROJECTION_MISSES),
            publications=_count(
                counters,
                _execution_keys.SOURCE_IMAGE_PROJECTION_PUBLICATIONS,
            ),
        ),
        construction=TemporalConstruction(
            postorder_frames=_count(
                counters, _execution_keys.SOURCE_IMAGE_POSTORDER_FRAMES
            ),
            primitive_applications=_count(
                counters,
                _execution_keys.SOURCE_IMAGE_PRIMITIVE_APPLICATIONS,
            ),
            chronological_compositions=_count(
                counters,
                _execution_keys.SOURCE_IMAGE_CHRONOLOGICAL_COMPOSITIONS,
            ),
            composite_applications=_count(
                counters, "source_image_composite_applications"
            ),
            demanded_composite_applications=_count(
                counters, "source_image_demanded_composite_applications"
            ),
            source_image_publications=source_publications,
            source_image_adapter_registrations=_count(
                counters, _execution_keys.SOURCE_IMAGE_ADAPTER_REGISTRATIONS
            ),
            arithmetic_result_publications=_count(
                counters, "arithmetic_result_publications"
            ),
            bootstrap_admission_steps=bootstrap,
            reverse_pair_steps=_count(
                counters, _reverse_add_keys.REVERSE_Q19_PRIMITIVE_PAIR_APPLICATIONS
            ),
            reverse_pair_sections=_count(
                counters, _reverse_add_keys.REVERSE_Q19_PAIR_OUTPUT_NODES_VISITED
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
            point_requests=_count(counters, _shared_keys.TEMPORAL_POINT_REQUESTS),
            length_requests=_count(counters, _shared_keys.TEMPORAL_LENGTH_REQUESTS),
        ),
        stream=_stream_demand(counters),
        rendering=TemporalRenderingWork(
            requests=_count(counters, _api_keys.CLI_RENDER_REQUESTS),
            emitted_digits=_count(counters, _api_keys.CLI_RENDER_EMITTED_DIGITS),
            failures=_count(counters, _api_keys.CLI_RENDER_FAILURES),
            integer_conversion_operand_bits=_count(
                counters, _api_keys.CLI_RENDER_INTEGER_CONVERSION_OPERAND_BITS
            ),
        ),
        affine_width=TemporalAffineWidth(
            requests=_count(counters, _fields_keys.AFFINE_WIDTH_REQUESTS),
            operand_bits=_count(counters, _fields_keys.AFFINE_WIDTH_OPERAND_BITS),
            interval_checks=_count(counters, _fields_keys.AFFINE_WIDTH_INTERVAL_CHECKS),
            refinements=_count(counters, _fields_keys.AFFINE_WIDTH_REFINEMENTS),
            exact_boundaries=_count(
                counters, _fields_keys.AFFINE_WIDTH_EXACT_BOUNDARIES
            ),
            failures=_count(counters, _fields_keys.AFFINE_WIDTH_FAILURES),
        ),
        growth_readout=TemporalGrowthReadout(
            work=_count(counters, _fields_keys.GROWTH_ARITHMETIC_WORK),
            operand_bits=_count(counters, _fields_keys.GROWTH_ARITHMETIC_OPERAND_BITS),
            precision_bits=_count(
                counters, _fields_keys.GROWTH_ARITHMETIC_PRECISION_BITS
            ),
            refinements=_count(counters, _fields_keys.GROWTH_ORDER_REFINEMENTS),
            exact_rational_cases=_count(
                counters, _fields_keys.GROWTH_ORDER_EXACT_RATIONAL_CASES
            ),
            bounded_exact_ratio_cases=_count(
                counters,
                _fields_keys.GROWTH_ORDER_BOUNDED_EXACT_RATIO_CASES,
            ),
            identity_shortcuts=_count(
                counters, _fields_keys.GROWTH_ORDER_IDENTITY_SHORTCUTS
            ),
            log_constant_hits=_count(
                counters, _fields_keys.GROWTH_LOG_CONSTANT_CACHE_HITS
            ),
            cf_requests=_count(counters, _fields_keys.GROWTH_CF_KEY_LOOKUPS),
            cf_budget_refusals=_count(counters, _fields_keys.GROWTH_CF_BUDGET_REFUSALS),
            order_hits=_count(counters, _fields_keys.GROWTH_ORDER_CACHE_HITS),
            budget_refusals=_count(
                counters, _shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS
            ),
        ),
        observations=TemporalObservations(
            collatz_two_sided_cylinder_constructions=_count(
                counters, _collatz_keys.COLLATZ_TWO_SIDED_CYLINDER_CONSTRUCTIONS
            ),
            collatz_two_sided_cylinder_operand_bits=_count(
                counters, _collatz_keys.COLLATZ_TWO_SIDED_CYLINDER_OPERAND_BITS
            ),
            collatz_radix6_coverage_evaluations=_count(
                counters, _collatz_keys.COLLATZ_RADIX6_COVERAGE_EVALUATIONS
            ),
            collatz_radix6_coverage_operand_bits=_count(
                counters, _collatz_keys.COLLATZ_RADIX6_COVERAGE_OPERAND_BITS
            ),
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
                counters, _antihydra_keys.MAHLER_SOURCE_COMPOSED_IMAGE_READS
            ),
            mahler_associated_action_demands=_count(
                counters, _antihydra_keys.MAHLER_ASSOCIATED_ACTION_DEMANDS
            ),
            mahler_root_shell_projections=_count(
                counters, _antihydra_keys.MAHLER_ROOT_SHELL_PROJECTIONS
            ),
            mahler_root_shell_operand_bits=_count(
                counters, _antihydra_keys.MAHLER_ROOT_SHELL_OPERAND_BITS
            ),
            mahler_center_matrix_demands=_count(
                counters, _antihydra_keys.MAHLER_CENTER_MATRIX_DEMANDS
            ),
            mahler_center_matrix_physical_steps=_count(
                counters, _antihydra_keys.MAHLER_CENTER_MATRIX_PHYSICAL_STEPS
            ),
            physical_roof_evaluations=_count(counters, "physical_roof_evaluations"),
            query_observer_reuses=_count(counters, "query_observer_reuses"),
            higher_concrete_operation_evaluations=_count(
                counters,
                _execution_keys.HIGHER_CONCRETE_OPERATION_EVALUATIONS,
            ),
            higher_action_continuation_requests=_count(
                counters,
                _execution_keys.HIGHER_ACTION_CONTINUATION_REQUESTS,
            ),
            reverse_recursive_pair_width_cache_hits=_count(
                counters, _reverse_add_keys.REVERSE_RECURSIVE_PAIR_WIDTH_CACHE_HITS
            ),
            reverse_recursive_pair_width_cache_misses=_count(
                counters, _reverse_add_keys.REVERSE_RECURSIVE_PAIR_WIDTH_CACHE_MISSES
            ),
            reverse_recursive_pair_width_publications=_count(
                counters, _reverse_add_keys.REVERSE_RECURSIVE_PAIR_WIDTH_PUBLICATIONS
            ),
            reverse_recursive_pair_width_descents=_count(
                counters, _reverse_add_keys.REVERSE_RECURSIVE_PAIR_WIDTH_DESCENTS
            ),
            reverse_recursive_pair_width_failures=_count(
                counters, _reverse_add_keys.REVERSE_RECURSIVE_PAIR_WIDTH_FAILURES
            ),
            reverse_q19_temporal_ring_constraint_cells=_count(
                counters, _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_CONSTRAINT_CELLS
            ),
            reverse_q19_temporal_ring_propagation_rounds=_count(
                counters, _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_PROPAGATION_ROUNDS
            ),
            reverse_q19_temporal_ring_output_lane_visits=_count(
                counters, _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_OUTPUT_LANE_VISITS
            ),
            reverse_q19_temporal_ring_failures=_count(
                counters, _reverse_add_keys.REVERSE_Q19_TEMPORAL_RING_FAILURES
            ),
            reverse_q19_inward_symmetric_filter_value_visits=_count(
                counters,
                _reverse_add_keys.REVERSE_Q19_INWARD_SYMMETRIC_FILTER_VALUE_VISITS,
            ),
            reverse_q19_directed_diagonal_inlet_visits=_count(
                counters, _reverse_add_keys.REVERSE_Q19_DIRECTED_DIAGONAL_INLET_VISITS
            ),
            reverse_q19_border_width_power_requests=_count(
                counters, _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_POWER_REQUESTS
            ),
            reverse_q19_border_width_power_refusals=_count(
                counters, _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_POWER_REFUSALS
            ),
            reverse_q19_border_width_state_visits=_count(
                counters, _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_STATE_VISITS
            ),
            reverse_q19_border_width_states=_count(
                counters, _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_STATES
            ),
            reverse_q19_border_width_edges=_count(
                counters, _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_EDGES
            ),
            reverse_q19_border_width_composition_pairs=_count(
                counters, _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_COMPOSITION_PAIRS
            ),
            reverse_q19_border_width_relation_cells=_count(
                counters, _reverse_add_keys.REVERSE_Q19_BORDER_WIDTH_RELATION_CELLS
            ),
            double_reverse_birth_layer_source_port_reads=_count(
                counters,
                _double_reverse_keys.DOUBLE_REVERSE_BIRTH_LAYER_SOURCE_PORT_READS,
            ),
            double_reverse_birth_layer_strip_steps=_count(
                counters, _double_reverse_keys.DOUBLE_REVERSE_BIRTH_LAYER_STRIP_STEPS
            ),
            double_reverse_birth_layer_model_states=_count(
                counters, _double_reverse_keys.DOUBLE_REVERSE_BIRTH_LAYER_MODEL_STATES
            ),
            double_reverse_birth_layer_induction_rows=_count(
                counters, _double_reverse_keys.DOUBLE_REVERSE_BIRTH_LAYER_INDUCTION_ROWS
            ),
            double_reverse_birth_layer_period_comparisons=_count(
                counters,
                _double_reverse_keys.DOUBLE_REVERSE_BIRTH_LAYER_PERIOD_COMPARISONS,
            ),
            double_reverse_birth_layer_publications=_count(
                counters, _double_reverse_keys.DOUBLE_REVERSE_BIRTH_LAYER_PUBLICATIONS
            ),
            double_reverse_birth_layer_refusals=_count(
                counters, _double_reverse_keys.DOUBLE_REVERSE_BIRTH_LAYER_REFUSALS
            ),
            double_reverse_open_ring_source_ports=_count(
                counters, _double_reverse_keys.DOUBLE_REVERSE_OPEN_RING_SOURCE_PORTS
            ),
            double_reverse_open_ring_window_publications=_count(
                counters,
                _double_reverse_keys.DOUBLE_REVERSE_OPEN_RING_WINDOW_PUBLICATIONS,
            ),
            double_reverse_open_ring_moore_publications=_count(
                counters,
                _double_reverse_keys.DOUBLE_REVERSE_OPEN_RING_MOORE_PUBLICATIONS,
            ),
            double_reverse_open_ring_guard_refusals=_count(
                counters, _double_reverse_keys.DOUBLE_REVERSE_OPEN_RING_GUARD_REFUSALS
            ),
        ),
        family_work=tuple(families),
        comma=TemporalCommaWork(
            operations=_count(counters, _comma_keys.COMMA_WORK),
            binary_compositions=_count(counters, "comma_binary_composition_work"),
            transfer_constructions=_count(
                counters, _comma_keys.COMMA_TRANSFER_CONSTRUCTIONS
            ),
            transfer_phase_terms=_count(
                counters, _comma_keys.COMMA_TRANSFER_PHASE_TERMS
            ),
            cycle_rule_evaluations=_count(
                counters, _comma_keys.COMMA_CYCLE_RULE_EVALUATIONS
            ),
            child_candidate_checks=_count(
                counters, _comma_keys.COMMA_CHILD_CANDIDATE_CHECKS
            ),
            seam_predicate_check_bound=_count(
                counters, _comma_keys.COMMA_SEAM_PREDICATE_CHECKS
            ),
            operand_bits=_count(counters, _comma_keys.COMMA_OPERAND_BIT_WORK),
            represented_phase_cycles=_count(counters, _comma_keys.COMMA_PHASE_CYCLES),
            powered_image_applications=_count(
                counters, _comma_keys.COMMA_POWERED_IMAGE_APPLICATIONS
            ),
            represented_transitions=_count(
                counters, _comma_keys.COMMA_REPRESENTED_TRANSITIONS
            ),
            evaluated_transitions=_count(
                counters, _comma_keys.COMMA_EVALUATED_TRANSITIONS
            ),
            seam_steps=_count(counters, _comma_keys.COMMA_SCALAR_SEAM_STEPS),
            relative_guard_checks=_count(
                counters, _comma_keys.COMMA_RELATIVE_GUARD_CHECKS
            ),
            relative_cycle_rebindings=_count(
                counters, _comma_keys.COMMA_RELATIVE_CYCLE_REBINDINGS
            ),
            boundary_template_hits=_count(
                counters, _comma_keys.COMMA_BOUNDARY_TEMPLATE_HITS
            ),
            boundary_template_misses=_count(
                counters, _comma_keys.COMMA_BOUNDARY_TEMPLATE_MISSES
            ),
            boundary_template_publications=_count(
                counters, _comma_keys.COMMA_BOUNDARY_TEMPLATE_PUBLICATIONS
            ),
            boundary_template_retained_nodes=_count(
                counters, _comma_keys.COMMA_BOUNDARY_TEMPLATE_RETAINED_NODES
            ),
            boundary_seal_checks=_count(
                counters, _comma_keys.COMMA_BOUNDARY_SEAL_CHECKS
            ),
            boundary_explicit_audit_component_checks=_count(
                counters, _comma_keys.COMMA_BOUNDARY_EXPLICIT_AUDIT_COMPONENT_CHECKS
            ),
            boundary_explicit_audit_operand_bits=_count(
                counters, _comma_keys.COMMA_BOUNDARY_EXPLICIT_AUDIT_OPERAND_BITS
            ),
            boundary_seal_retained_slots=_count(
                counters, _comma_keys.COMMA_BOUNDARY_SEAL_RETAINED_SLOTS
            ),
            boundary_seal_retained_integer_bits=_count(
                counters, _comma_keys.COMMA_BOUNDARY_SEAL_RETAINED_INTEGER_BITS
            ),
            boundary_prefix_applications=_count(
                counters, _comma_keys.COMMA_BOUNDARY_PREFIX_APPLICATIONS
            ),
            boundary_represented_transitions=_count(
                counters, _comma_keys.COMMA_BOUNDARY_REPRESENTED_TRANSITIONS
            ),
            stream_requests=_count(counters, "comma_stream_requests"),
            stream_emitted_digits=_count(counters, "comma_stream_emitted_digits"),
            stream_workspace_peak_slots=_count(
                counters, "comma_stream_workspace_peak_slots"
            ),
            stream_workspace_peak_integer_bits=_count(
                counters, "comma_stream_workspace_peak_integer_bits"
            ),
            certificate_operations=_count(counters, _comma_keys.COMMA_CERTIFICATE_WORK),
            certificate_sector_entries=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_SECTOR_ENTRIES
            ),
            certificate_boundary_classifications=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_BOUNDARY_CLASSIFICATIONS
            ),
            certificate_candidate_digit_trials=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_CANDIDATE_DIGIT_TRIALS
            ),
            certificate_operand_bits=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_OPERAND_BIT_WORK
            ),
            certificate_read_bytes=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_READ_BYTES
            ),
            certificate_uncompressed_bytes=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_UNCOMPRESSED_BYTES
            ),
            certificate_frontier_peak=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_FRONTIER_PEAK
            ),
            certificate_local_hits=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_LOCAL_HITS
            ),
            certificate_cache_hits=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_CACHE_HITS
            ),
            certificate_cache_misses=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_CACHE_MISSES
            ),
            certificate_cache_bypasses=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_CACHE_BYPASSES
            ),
            certificate_cache_publications=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_CACHE_PUBLICATIONS
            ),
            budget_refusals=_count(counters, _comma_keys.COMMA_BUDGET_REFUSALS),
            certificate_budget_refusals=_count(
                counters, _comma_keys.COMMA_CERTIFICATE_BUDGET_REFUSALS
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


__all__ = [
    "METRICS_SCHEMA_VERSION",
    "TemporalAffineWidth",
    "TemporalCommaWork",
    "TemporalConstruction",
    "TemporalDemand",
    "TemporalExecutionDiagnostics",
    "TemporalFamilyWork",
    "TemporalGrowthReadout",
    "TemporalMacrocellWork",
    "TemporalObservations",
    "TemporalRenderingWork",
    "TemporalReportingWork",
    "TemporalResources",
    "TemporalStreamDemand",
]
