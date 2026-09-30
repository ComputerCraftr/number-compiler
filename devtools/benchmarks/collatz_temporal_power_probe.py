"""Release probe for source-bound physical-Collatz image construction."""

from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import asdict
from importlib import import_module
from random import Random
from time import perf_counter

from devtools.benchmarks.reporting import write_json_report
from devtools.benchmarks.temporal_probe_support import (
    common_temporal_blockers,
    shared_cutover_sources,
)
from devtools.benchmarks.tile_projection_accounting import (
    projection_accounting,
)
from devtools.checks.dependency_graph import source_syntax
from devtools.checks.test_run_evidence import source_fingerprint
from devtools.paths import report_directory, repository_root
from devtools.runs import run_reported
from number_compiler.api.cli_context import QueryContext
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.number_api import (
    AntihydraTermPayload,
    NumberCompiler,
    PoweredCollatzTermPayload,
)
from number_compiler.resources.collatz_power_metrics import CollatzPhysicalBlockMetrics
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

ROOT = repository_root()

CONSTRUCTION_STEPS = (16, 256, 1_000_000, 10**18)
PROJECTION_STEPS = (16, 32, 64, 128, 256)


def _required_work(metrics: CollatzPhysicalBlockMetrics, name: str) -> int:
    """A missing production instrument is missing evidence, not zero work."""
    counters = metrics.resource_work_counters
    value = counters.get(name)
    if type(value) is not int:
        raise AssertionError(("source-image-work-measurement-missing", name))
    return value


def _source_image_work(metrics: CollatzPhysicalBlockMetrics) -> tuple[int, int, int]:
    """Charge operations, operand bits, and seal bytes in distinct units."""
    counters = metrics.resource_work_counters
    prefixes = ("source_image_", "collatz_physical_", "collatz_image_")
    operations = 0
    operand_bits = 0
    seal_bytes = 0
    for name, value in counters.items():
        if not name.startswith(prefixes):
            continue
        if type(value) is not int or value < 0:
            raise AssertionError(("invalid-source-image-work-measurement", name, value))
        if name.endswith(("_symbols", "_ticks", "_repetitions", "_peak_bits")):
            # Represented extent and high-water storage are not performed work.
            continue
        if "operand_bits" in name or name.endswith("_bits"):
            operand_bits += value
        elif name.endswith("_bytes"):
            seal_bytes += value
        elif not (name.endswith(("_peak", "_extent"))):
            operations += value
    return operations, operand_bits, seal_bytes


def _metric_int(value: object) -> int:
    if type(value) is not int:
        raise AssertionError(("probe-metric-is-not-an-exact-integer", value))
    return value


def _physical(value: int) -> int:
    return 3 * value + 1 if value & 1 else value // 2


def _scalar(seed: int, steps: int) -> int:
    value = int(seed)
    for _ in range(int(steps)):
        value = _physical(value)
    return value


def _construction_rows() -> list[dict[str, int | float]]:
    rows = []
    for steps in CONSTRUCTION_STEPS:
        started = perf_counter()
        term = PoweredCollatzTerm(27, steps)
        elapsed = perf_counter() - started
        metrics = term.metrics()
        bits = max(1, steps.bit_length())
        if metrics.operator_nodes > 4 * bits or metrics.compose_operations > 4 * bits:
            raise AssertionError((steps, metrics))
        if metrics.point_queries or metrics.direct_powered_point_queries:
            raise AssertionError(("construction-executed-endpoint", steps))
        rows.append(
            {
                "steps": steps,
                "index_bits": bits,
                "operator_nodes": metrics.operator_nodes,
                "compose_operations": metrics.compose_operations,
                "syntax_depth_bound": metrics.syntax_depth_bound,
                "construction_seconds": elapsed,
                "point_queries": metrics.point_queries,
            }
        )
    return rows


def _projection_rows() -> list[dict[str, object]]:
    rows = []
    for steps in PROJECTION_STEPS:
        term = PoweredCollatzTerm(27, steps)
        expected = _scalar(27, steps)
        started = perf_counter()
        low = term.digit(0)
        elapsed = perf_counter() - started
        if low != (expected & 1):
            raise AssertionError((steps, low, expected))
        first_publications = dict(term._ledger.counters)
        metrics = term.metrics()
        behavior = term.behavior_metrics()
        if term.digit(0) != low:
            raise AssertionError(("source-image-replay-mismatch", steps, low))
        replay_publications = term._ledger.counters
        diagnostic = metrics.temporal_diagnostics
        if diagnostic.schema_version != metrics.metrics_schema_version:
            raise AssertionError(("temporal-diagnostic-schema-mismatch", steps))
        scheduler_work = projection_accounting(metrics)
        image_work = {
            name: _required_work(metrics, name)
            for name in (
                "collatz_physical_action_publications",
                "source_image_postorder_frames",
                "source_image_publications",
                "source_image_projection_publications",
                "collatz_image_radix_demands",
            )
        }
        if any(value <= 0 for value in image_work.values()):
            raise AssertionError(
                ("source-image-construction-not-observed", steps, image_work)
            )
        for name in (
            "collatz_physical_macro_requests",
            "collatz_physical_macro_bounded_base_steps",
            "collatz_physical_macro_compositions",
            "collatz_physical_transient_leaf_steps",
            "collatz_physical_temporal_run_actions",
            "source_image_primitive_applications",
        ):
            # These are mutually exclusive construction paths. An unexecuted
            # path contributes zero here, while required publication above
            # must still have an explicit measurement.
            image_work[name] = metrics.resource_work_counters.get(name, 0)
        discovery_steps = (
            image_work["collatz_physical_macro_bounded_base_steps"]
            + image_work["collatz_physical_transient_leaf_steps"]
            + image_work["collatz_physical_temporal_run_actions"]
        )
        if discovery_steps <= 0:
            raise AssertionError(("source-discovery-measurement-missing", steps))
        family_work = tuple(
            work
            for work in diagnostic.family_work
            if work.counter_prefix == "collatz_physical"
        )
        if (
            len(family_work) != 1
            or family_work[0].bounded_base_steps
            != metrics.resource_work_counters.get(
                "collatz_physical_macro_bounded_base_steps"
            )
            or diagnostic.construction.source_image_publications
            != image_work["source_image_publications"]
            or diagnostic.projection.publications
            != image_work["source_image_projection_publications"]
        ):
            raise AssertionError(("source-image-diagnostic-incomplete", steps))
        image_action_work, image_operand_bits, image_seal_bytes = _source_image_work(
            metrics
        )
        # A single admitted <=64-step leaf has no chronological join; absence
        # of that operation counter is an exact zero for this bounded case.
        chronological = metrics.resource_work_counters.get(
            "source_image_chronological_compositions", 0
        )
        if type(chronological) is not int or chronological < 0:
            raise AssertionError(("invalid-chronological-work", steps, chronological))
        if steps > 64 and (
            chronological != 0
            or image_work["source_image_primitive_applications"] != 0
            or (
                metrics.resource_work_counters.get(
                    "collatz_physical_composite_cutover_publications", 0
                )
                + metrics.resource_work_counters.get(
                    "collatz_physical_run_contraction_publications", 0
                )
            )
            <= 0
        ):
            raise AssertionError(("direct-composite-cutover-missing", steps))
        if metrics.direct_powered_point_queries != 1:
            raise AssertionError(("not-direct-point", steps, metrics))
        if not metrics.resource_audit_complete or metrics.resource_accounting_mismatch:
            raise AssertionError(("incomplete-resource-inventory", steps, metrics))
        if (
            metrics.forbidden_future_payloads
            or metrics.retained_unbounded_future_integers
        ):
            raise AssertionError(("future-payload-retained", steps, metrics))
        rows.append(
            {
                **scheduler_work,
                **image_work,
                "temporal_diagnostics": asdict(diagnostic),
                "source_image_chronological_compositions": chronological,
                "source_image_operand_bits": image_operand_bits,
                "source_image_seal_bytes": image_seal_bytes,
                "source_image_operation_work": image_action_work,
                "source_image_bounded_base_steps": discovery_steps,
                "runtime_image_matches_scalar": low == (expected & 1),
                "source_image_replay_publications_stable": (
                    replay_publications.get("source_image_publications", 0)
                    == first_publications.get("source_image_publications", 0)
                    and replay_publications.get(
                        "source_image_projection_publications", 0
                    )
                    == first_publications.get("source_image_projection_publications", 0)
                ),
                "resource_accounting_exact": (
                    metrics.resource_audit_complete == 1
                    and metrics.resource_accounting_mismatch == 0
                ),
                "steps": steps,
                "index_bits": max(1, steps.bit_length()),
                "schema_version": metrics.metrics_schema_version,
                "resource_audit_complete": metrics.resource_audit_complete,
                "resource_accounting_mismatch": metrics.resource_accounting_mismatch,
                "forbidden_future_payloads": metrics.forbidden_future_payloads,
                "retained_unbounded_future_integers": metrics.retained_unbounded_future_integers,
                "retained_entries": metrics.resource_ledger_entries,
                "cache_slots": metrics.cache_slots,
                "exact_source_occurrences": metrics.exact_source_occurrences,
                "spatial_occurrence_bindings": metrics.spatial_occurrence_bindings,
                "spatial_binding_nodes": metrics.spatial_binding_nodes,
                "canonical_transfer_nodes": metrics.canonical_transfer_nodes,
                "temporal_program_nodes": metrics.temporal_program_nodes,
                "finite_port_state_nodes": metrics.finite_port_state_nodes,
                "other_retained_nodes": metrics.other_retained_nodes,
                "retained_nodes": metrics.resource_ledger_nodes,
                "maximum_arithmetic_bits": metrics.maximum_arithmetic_bits,
                "bounded_limb_operations": metrics.bounded_limb_operations,
                "higher_concrete_operation_evaluations": metrics.higher_concrete_operation_evaluations,
                "low_bit": low,
                "projection_seconds": elapsed,
                "operator_nodes": metrics.operator_nodes,
                "direct_powered_point_queries": metrics.direct_powered_point_queries,
                "retained_spacetime_nodes": metrics.retained_execution_nodes,
                "canonical_history_word_roots": metrics.canonical_program_word_roots,
                "canonical_spacetime_macrocell_roots": metrics.canonical_spacetime_macrocell_roots,
                "recursive_action_left_nodes": metrics.recursive_action_left_nodes,
                "recursive_action_right_nodes": metrics.recursive_action_right_nodes,
                "recursive_value_cache_entries": metrics.recursive_value_cache_entries,
                "spacetime_macro_cache_hits": metrics.spacetime_macro_cache_hits,
                "spacetime_macro_cache_misses": metrics.spacetime_macro_cache_misses,
                "spacetime_macro_cache_entries": metrics.spacetime_macro_cache_entries,
                "raw_spacetime_boundary_cache_entries": metrics.raw_spacetime_boundary_cache_entries,
                "retained_cache_accounting_delta": metrics.retained_cache_accounting_delta,
                "sparse_carrier_layers_left": metrics.sparse_carrier_layers_left,
                "sparse_carrier_layers_right": metrics.sparse_carrier_layers_right,
                "spacetime_tile_output_entries": metrics.spacetime_tile_output_entries,
                "spacetime_tile_output_max_level": metrics.spacetime_tile_output_max_level,
                "spacetime_temporal_absorption_max": metrics.spacetime_temporal_absorption_max,
                "left_boundary_residuals": metrics.left_boundary_residuals,
                "right_boundary_residuals": metrics.right_boundary_residuals,
                "bounded_application_enabled": metrics.bounded_application_enabled,
                "bounded_temporal_state_classes": metrics.bounded_application_temporal_state_classes,
                "bounded_temporal_action_classes": metrics.bounded_application_temporal_action_classes,
                "bounded_exact_spatial_occurrences": metrics.bounded_application_exact_spatial_occurrences,
                "bounded_symbolic_action_nodes": metrics.bounded_application_symbolic_action_nodes,
                "bounded_jump_entries": metrics.bounded_application_jump_entries,
                "bounded_primitive_step_evaluations": metrics.bounded_application_primitive_step_evaluations,
                "bounded_residual_physical_steps": metrics.bounded_application_residual_physical_steps,
                "temporal_parent_requests": metrics.temporal_parent_requests,
                "temporal_parent_early_hits": metrics.temporal_parent_early_hits,
                "temporal_parent_compositions": metrics.temporal_parent_compositions,
                "whole_word_sweeps": metrics.whole_word_sweeps,
                "whole_word_symbol_visits": metrics.whole_word_symbol_visits,
                "proof_machine_applications": metrics.proof_machine_applications,
                "new_canonical_field_images_published": metrics.new_canonical_field_images_published,
                "field_image_nodes": metrics.field_image_nodes,
                "field_interface_nodes": metrics.field_interface_nodes,
                "total_internal_action_work": metrics.total_internal_action_work,
                "unquotiented_recursive_application_nodes": behavior.unquotiented_recursive_application_description_nodes,
            }
        )
    return rows


def _source_audit() -> dict[str, bool]:
    api = source_syntax(ROOT / "src" / "number_compiler" / "api/number_api.py")
    block = source_syntax(
        ROOT / "src" / "number_compiler" / "sequences/collatz/block_power.py"
    )
    (
        compatibility_names,
        compatibility_imports,
        _unused_runtime_binding,
        spacetime,
        boundary,
        _unused_router_syntax_binding,
        _unused_router_imports_binding,
        generic_executor_imported,
    ) = shared_cutover_sources(ROOT)
    init = source_syntax(ROOT / "src" / "number_compiler" / "__init__.py")
    bounded = source_syntax(
        ROOT
        / "src"
        / "number_compiler"
        / "hashlife"
        / "execution"
        / "bounded_application.py"
    )
    public_modules = init.imports | init.export_modules | init.dynamic_imports
    checks = {
        "number_api_has_no_orbit_builder": "collatz_orbit_formulas"
        not in api.identifiers,
        "number_api_has_no_ternary_orbit_builder": "collatz_orbit_formulas_ternary"
        not in api.identifiers,
        "number_api_has_no_composite_orbit_builder": "collatz_orbit_formulas_local_composite_radix"
        not in api.identifiers,
        "powered_term_has_no_causal_engine": "CollatzCausalSpacetimeEngine"
        not in block.identifiers,
        "slow_causal_engine_not_public": not any(
            name.endswith("collatz_spacetime") for name in public_modules
        )
        and "CollatzCausalSpacetimeEngine" not in init.exports,
        "legacy_germ_cache_not_public": not any(
            name.endswith("collatz_germ_cache") for name in public_modules
        ),
        "accelerated_reference_power_not_public": "collatz_affine_suffix_event_power_word"
        not in init.identifiers
        and "collatz_affine_suffix_event_power_word" not in init.exports
        and "collatz_affine_suffix_event_power_value" not in init.identifiers
        and "collatz_affine_suffix_event_power_value" not in init.exports,
        "history_word_carrier_deleted": "..program_word" not in compatibility_imports
        and "CanonicalWord" not in compatibility_names,
        "exact_future_tile_output_deleted": "_output_tile_macro"
        not in spacetime.functions,
        "certified_family_has_no_generic_executor_import": not generic_executor_imported,
        "raw_spacetime_boundary_runtime_deleted": (
            "SpacetimeBoundary" not in compatibility_names
            and "intern_boundary" not in compatibility_names
            and "_intern_spacetime_state" not in compatibility_names
            and "_advance_effect_boundary" not in compatibility_names
        ),
        "generic_recursive_carrier_available_for_other_effects": "_RecursiveBoundaryState"
        in compatibility_names,
        "bounded_temporal_application_boundary_present": "build_certified_field_application"
        in bounded.identifiers,
        "raw_boundary_carrier_class_deleted": "SpacetimeBoundary"
        not in boundary.classes,
    }
    if not all(checks.values()):
        raise AssertionError(checks)
    return checks


def run_probe() -> dict[str, object]:
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

    rejection: UnsupportedInterfaceError | None = None
    try:
        projection = _projection_rows()
    except UnsupportedInterfaceError as error:
        projection = []
        rejection = error
    exact: dict[str, int] = {}
    if rejection is None:
        compiler = NumberCompiler()
        exact = {
            str(radix): compiler.nth("collatz", 10, seed=27, radix=radix)
            for radix in (2, 3, 6)
        }
        if set(exact.values()) != {214}:
            raise AssertionError(exact)
    tail_sublinear = False
    if len(projection) >= 2:
        prev, tail = projection[-2], projection[-1]
        prev_steps = _metric_int(prev["source_image_bounded_base_steps"])
        tail_steps = _metric_int(tail["source_image_bounded_base_steps"])
        tail_sublinear = prev_steps > 0 and tail_steps < 2 * prev_steps
    runtime_image_contract = bool(projection) and all(
        bool(row["runtime_image_matches_scalar"])
        and bool(row["source_image_replay_publications_stable"])
        and bool(row["resource_accounting_exact"])
        and _metric_int(row["source_image_publications"]) > 0
        and _metric_int(row["unquotiented_recursive_application_nodes"]) == 0
        and _metric_int(row["sequential_generation_advances"]) == 0
        and _metric_int(row["recursive_value_cache_entries"]) == 0
        for row in projection
    )
    work_envelope = True
    if len(projection) > 1:
        bootstrap = _metric_int(projection[0]["source_image_operation_work"])
        work_envelope = all(
            _metric_int(current["source_image_operation_work"])
            <= 2 * _metric_int(previous["source_image_operation_work"]) + bootstrap
            for previous, current in itertools.pairwise(projection)
        )
    byte_envelope = True
    if len(projection) > 1:
        bootstrap_bytes = _metric_int(projection[0]["source_image_seal_bytes"])
        byte_envelope = all(
            _metric_int(current["source_image_seal_bytes"])
            <= 2 * _metric_int(previous["source_image_seal_bytes"]) + bootstrap_bytes
            for previous, current in itertools.pairwise(projection)
        )
    operand_envelope = True
    if len(projection) > 1:
        bootstrap_bits = _metric_int(projection[0]["source_image_operand_bits"])
        operand_envelope = all(
            _metric_int(current["source_image_operand_bits"])
            <= 2 * _metric_int(previous["source_image_operand_bits"]) + bootstrap_bits
            for previous, current in itertools.pairwise(projection)
        )
    retention_envelope = len(projection) > 1 and all(
        _metric_int(current["retained_entries"])
        <= 2 * _metric_int(previous["retained_entries"])
        + _metric_int(projection[0]["retained_entries"])
        and _metric_int(current["retained_nodes"])
        <= 2 * _metric_int(previous["retained_nodes"])
        + _metric_int(projection[0]["retained_nodes"])
        for previous, current in itertools.pairwise(projection)
    )
    blockers = common_temporal_blockers(projection, rejection, _metric_int)
    if projection and not all(
        _metric_int(row["source_image_chronological_compositions"])
        <= 2 * max(1, _metric_int(row["index_bits"])) + 4
        for row in projection
    ):
        blockers.append("source_image_composition_exceeds_binary_envelope")
    if projection and not all(
        _metric_int(row["source_image_publications"]) > 0
        and _metric_int(row["source_image_projection_publications"]) > 0
        for row in projection
    ):
        blockers.append("certified_path_published_no_source_images")
    if not retention_envelope:
        blockers.append("source_image_retention_exceeds_doubling_envelope")
    if not work_envelope:
        blockers.append("internal_action_work_exceeds_doubling_envelope")
    if not operand_envelope:
        blockers.append("source_image_operand_bits_exceed_doubling_envelope")
    if not byte_envelope:
        blockers.append("source_image_seal_bytes_exceed_doubling_envelope")
    if any(
        _metric_int(current["source_image_operation_work"])
        > 2 * _metric_int(previous["source_image_operation_work"]) + 64
        for previous, current in itertools.pairwise(projection)
    ):
        blockers.append("source_image_work_exceeds_doubling_envelope")
    if not runtime_image_contract:
        blockers.append("source_image_runtime_contract_unverified")
    measured_scaling_gate = "PASS" if not blockers else "BLOCKED"
    return {
        "version": "0.62.0-schema8-source-image-observation",
        "schema_version": 8,
        "status": "RED" if blockers else "GREEN",
        "construction": _construction_rows(),
        "projection": projection,
        "execution_available": rejection is None,
        "execution_status": "available" if rejection is None else "unavailable",
        "measurements_complete": rejection is None and bool(projection),
        "measured_scaling_gate": measured_scaling_gate,
        "release_blockers": blockers,
        "source_image_retention_envelope": retention_envelope,
        "execution_rejection_type": (
            None if rejection is None else type(rejection).__name__
        ),
        "execution_rejection_reason": None if rejection is None else str(rejection),
        "source_audit": _source_audit(),
        "public_radix_exactness": exact,
        "public_radix_exactness_available": rejection is None,
        "source_image_runtime_contract": runtime_image_contract,
        "representative_seed_tail_sublinear": tail_sublinear,
    }


def balanced_scaling(
    family: str,
    indices: tuple[int, ...],
    trials: int,
    mode: str,
    pattern: str,
    mahler: bool,
) -> dict[str, object]:
    """Measure public construction, read-only reporting and full audit separately.

    The independent scalar reference runs outside all reported timings. Its
    cost is test-oracle work, not evidence for the production construction.
    """
    fingerprint = source_fingerprint(ROOT)
    rows: list[dict[str, object]] = []
    for steps in indices:
        seed = (
            (Random(407 + steps).getrandbits(steps) | (1 << (steps - 1)) | 1)
            if pattern == "random"
            else ((1 << steps) - 1) // 3 | (1 << (steps - 1)) | 1
            if pattern == "repeating"
            else 931386509544713451
            if pattern == "long"
            else 27
        )
        if family == "antihydra":
            seed = 8
        expected = seed
        for _ in range(steps):
            expected = (
                _physical(expected) if family == "collatz" else expected + expected // 2
            )
        arguments = [family, "--nth", str(steps), "--info", "metrics"]
        if family == "collatz":
            arguments += ["--seed", str(seed)]
        else:
            arguments += [
                "--max-steps",
                str(max(4096, steps)),
                "--max-state-bits",
                str(max(4096, 2 * steps)),
            ]
            if mahler:
                arguments += ["--info", "mahler"]
        request = parse_request(arguments)
        assert request is not None
        retained = NumberCompiler()
        if mode == "repeat":
            warm = QueryContext(request, retained)
            warm.term.materialize(max_bits=1_000_000)
            warm.information()
            warm_payload = warm.term.payload
            assert isinstance(
                warm_payload, (AntihydraTermPayload, PoweredCollatzTermPayload)
            )
            collect_ledger_metrics(
                warm_payload.term.ledger
                if isinstance(warm_payload, AntihydraTermPayload)
                else warm_payload.term._ledger
            )
        for trial in range(trials):
            if mode == "cold":
                NumberCompiler.clear_shared_cache()
            compiler = (
                retained
                if mode == "repeat"
                else NumberCompiler(
                    shared_cache=mode != "bypass",
                    max_cached_terms=0 if mode == "bypass" else 8,
                )
            )
            start = perf_counter()
            query = QueryContext(request, compiler)
            projected = query.term
            payload = projected.payload
            assert isinstance(
                payload, (AntihydraTermPayload, PoweredCollatzTermPayload)
            )
            ledger = (
                payload.term.ledger
                if isinstance(payload, AntihydraTermPayload)
                else payload.term._ledger
            )
            before = dict(ledger.counters)
            described = perf_counter()
            value = projected.materialize(max_bits=1_000_000)
            constructed = perf_counter()
            information = query.information()
            observed = perf_counter()
            rendered = str(value)
            emitted = perf_counter()
            audit = collect_ledger_metrics(ledger)
            audited = perf_counter()
            if value != expected or not audit.resource_audit_complete:
                raise AssertionError(
                    (family, steps, "endpoint or resource audit mismatch")
                )
            if audit.resource_accounting_mismatch:
                raise AssertionError((family, steps, "resource accounting mismatch"))
            counters = dict(ledger.counters)
            rows.append(
                {
                    "family": family,
                    "index": steps,
                    "index_unit": request.index_unit,
                    "seed_bits": seed.bit_length(),
                    "pattern": pattern if family == "collatz" else "source8",
                    "mode": mode,
                    "trial": trial,
                    "mahler_requested": mahler,
                    "value_bits": value.bit_length(),
                    "emitted_decimal_digits": len(rendered),
                    "descriptor_seconds": described - start,
                    "construction_seconds": constructed - described,
                    "observation_seconds": observed - constructed,
                    "render_seconds": emitted - observed,
                    "explicit_audit_seconds": audited - emitted,
                    "metrics": information["metrics"],
                    "work": counters,
                    "incremental_work": {
                        k: v - before.get(k, 0) for k, v in counters.items()
                    },
                    "entries": ledger.entries,
                    "nodes": ledger.nodes,
                    "peak_entries": ledger.peak_entries,
                    "peak_nodes": ledger.peak_nodes,
                }
            )
    after = source_fingerprint(ROOT)
    if after != fingerprint:
        raise AssertionError("source changed during temporal scaling probe")
    return {
        "source_before": fingerprint,
        "source_after": after,
        "scope": "public query in warm interpreter; full audit timed separately; finite workload evidence",
        "timing_scope": {
            "construction_seconds": "source-image construction plus exact endpoint demand",
            "render_seconds": "decimal conversion of the demanded integer",
            "incremental_work": "after descriptor creation; cumulative work includes descriptor costs",
        },
        "rows": rows,
    }


def limb_projection(
    indices: tuple[int, ...],
    trials: int,
    pattern: str,
    limb_widths: tuple[int, ...],
    limb_index: int,
) -> dict[str, object]:
    """Compare the public batched limb against independent binary payloads.

    Each timed side owns a fresh term and source image. The bounded scalar
    reference is evaluated before timing. These observations measure demand
    work after construction; they do not certify a faster source constructor.
    """
    # The payload imports the radix provider lazily. Exclude one-time Python
    # module loading from per-term demand work without warming any term/cache.
    import_module("number_compiler.projection.lazy_radix")
    fingerprint = source_fingerprint(ROOT)
    rows: list[dict[str, object]] = []
    for steps in indices:
        seed_bits = max(256, steps)
        seed = (
            (Random(407 + steps).getrandbits(seed_bits) | (1 << (seed_bits - 1)) | 1)
            if pattern == "random"
            else (1 << seed_bits) - 1
        )
        expected = _scalar(seed, steps)
        if expected in (1, 2, 4):
            raise AssertionError(("limb-probe-entered-cycle", steps, seed))
        for limb_bits in limb_widths:
            radix = 1 << limb_bits
            if limb_index * limb_bits >= expected.bit_length():
                raise ValueError(
                    "limb index must address an active digit for every requested width"
                )
            expected_limb = (expected >> (limb_bits * limb_index)) & (radix - 1)
            for trial in range(trials):
                # Direct PoweredCollatzTerm instances own distinct ledgers and
                # bypass the NumberCompiler process term cache by construction.
                started = perf_counter()
                limb_term = PoweredCollatzTerm(seed, steps)
                limb_payload = PoweredCollatzTermPayload(limb_term, radix)
                limb_described = perf_counter()
                limb_term._source_image()
                limb_constructed = perf_counter()
                limb_before = dict(limb_term._ledger.counters)
                limb_value = limb_payload.digit(limb_index)
                limb_observed = perf_counter()
                limb_cold = dict(limb_term._ledger.counters)
                limb_warm_value = limb_payload.digit(limb_index)
                limb_warmed = perf_counter()
                limb_warm = dict(limb_term._ledger.counters)

                bit_started = perf_counter()
                bit_term = PoweredCollatzTerm(seed, steps)
                bit_payload = PoweredCollatzTermPayload(bit_term, 2)
                bit_described = perf_counter()
                bit_term._source_image()
                bit_constructed = perf_counter()
                bit_before = dict(bit_term._ledger.counters)

                def bit_assembly(
                    width: int = limb_bits,
                    payload: PoweredCollatzTermPayload = bit_payload,
                ) -> int:
                    value = 0
                    for local_bit in range(width):
                        position = limb_index * width + local_bit
                        try:
                            bit = payload.digit(position)
                        except IndexError:
                            bit = 0
                        value |= bit << local_bit
                    return value

                bit_value = bit_assembly()
                bit_observed = perf_counter()
                bit_cold = dict(bit_term._ledger.counters)
                bit_warm_value = bit_assembly()
                bit_warmed = perf_counter()
                bit_warm = dict(bit_term._ledger.counters)
                if (
                    limb_value != expected_limb
                    or bit_value != expected_limb
                    or limb_warm_value != expected_limb
                    or bit_warm_value != expected_limb
                ):
                    raise AssertionError(
                        (
                            steps,
                            limb_bits,
                            limb_index,
                            expected_limb,
                            limb_value,
                            bit_value,
                        )
                    )

                def delta(
                    before: dict[str, int], after: dict[str, int], name: str
                ) -> int:
                    if name not in after:
                        raise AssertionError(("missing-limb-work-counter", name))
                    return after[name] - before.get(name, 0)

                limb_requests = delta(
                    limb_before, limb_cold, "direct_powered_point_queries"
                )
                bit_requests = delta(
                    bit_before, bit_cold, "direct_powered_point_queries"
                )
                if limb_requests != 1 or bit_requests != limb_bits:
                    raise AssertionError(
                        (
                            "limb-probe-missing-demand-work",
                            steps,
                            limb_requests,
                            bit_requests,
                        )
                    )
                rows.append(
                    {
                        "family": "collatz",
                        "index": steps,
                        "index_unit": "physical_step",
                        "seed_bits": seed.bit_length(),
                        "pattern": pattern,
                        "trial": trial,
                        "limb_bits": limb_bits,
                        "limb_index": limb_index,
                        "radix": radix,
                        "expected_limb": expected_limb,
                        "value_bits": expected.bit_length(),
                        "cache_mode": "independent_fresh_terms_no_process_cache",
                        "limb_descriptor_seconds": limb_described - started,
                        "limb_construction_seconds": limb_constructed - limb_described,
                        "limb_cold_projection_seconds": limb_observed
                        - limb_constructed,
                        "limb_warm_projection_seconds": limb_warmed - limb_observed,
                        "binary_descriptor_seconds": bit_described - bit_started,
                        "binary_construction_seconds": bit_constructed - bit_described,
                        "binary_cold_assembly_seconds": bit_observed - bit_constructed,
                        "binary_warm_assembly_seconds": bit_warmed - bit_observed,
                        "limb_cold_projection_requests": limb_requests,
                        "limb_warm_projection_requests": delta(
                            limb_cold, limb_warm, "direct_powered_point_queries"
                        ),
                        "limb_cold_radix_evaluations": delta(
                            limb_before, limb_cold, "collatz_image_radix_demands"
                        ),
                        "limb_warm_radix_evaluations": delta(
                            limb_cold, limb_warm, "collatz_image_radix_demands"
                        ),
                        "limb_cold_operand_bits": delta(
                            limb_before,
                            limb_cold,
                            "collatz_image_projection_operand_bits",
                        ),
                        "limb_warm_operand_bits": delta(
                            limb_cold,
                            limb_warm,
                            "collatz_image_projection_operand_bits",
                        ),
                        "binary_cold_point_requests": bit_requests,
                        "binary_warm_point_requests": delta(
                            bit_cold, bit_warm, "direct_powered_point_queries"
                        ),
                        "binary_cold_operand_bits": delta(
                            bit_before,
                            bit_cold,
                            "collatz_image_projection_operand_bits",
                        ),
                        "binary_warm_operand_bits": delta(
                            bit_cold,
                            bit_warm,
                            "collatz_image_projection_operand_bits",
                        ),
                        "limb_construction_work": {
                            key: value
                            for key, value in limb_before.items()
                            if key.startswith(("collatz_physical_", "source_image_"))
                        },
                        "binary_construction_work": {
                            key: value
                            for key, value in bit_before.items()
                            if key.startswith(("collatz_physical_", "source_image_"))
                        },
                    }
                )
    after = source_fingerprint(ROOT)
    if after != fingerprint:
        raise AssertionError("source changed during limb projection probe")
    return {
        "source_before": fingerprint,
        "source_after": after,
        "scope": "fresh public Collatz payloads; independent literal oracle outside timings",
        "construction_note": "source images constructed before projection timing; no CLI constructor speedup inferred",
        "rows": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--balanced-scaling", action="store_true")
    parser.add_argument("--limb-projection", action="store_true")
    parser.add_argument("--family", choices=("collatz", "antihydra"), default="collatz")
    parser.add_argument(
        "--indices", nargs="+", type=int, default=(16, 32, 64, 128, 256, 512, 1024)
    )
    parser.add_argument("--trials", type=int, default=5)
    parser.add_argument("--mode", choices=("cold", "repeat", "bypass"), default="cold")
    parser.add_argument(
        "--pattern", choices=("random", "repeating", "cycle", "long"), default="random"
    )
    parser.add_argument("--mahler", action="store_true")
    parser.add_argument("--limb-widths", nargs="+", type=int, default=(4, 32, 63))
    parser.add_argument("--limb-index", type=int, default=0)
    args = parser.parse_args()
    if args.trials < 1 or any(n < 1 or n > 8192 for n in args.indices):
        parser.error("positive trials and indices 1..8192 required")
    if args.mahler and args.family != "antihydra":
        parser.error("--mahler requires --family antihydra")
    if args.limb_projection:
        if args.balanced_scaling:
            parser.error("--limb-projection conflicts with --balanced-scaling")
        if args.family != "collatz" or args.mahler:
            parser.error("--limb-projection requires Collatz without Mahler")
        if args.pattern in ("cycle", "long"):
            parser.error(
                "--limb-projection requires a random or repeating source pattern"
            )
        if args.mode != "cold":
            parser.error("--limb-projection always uses independent fresh terms")
        if args.limb_index < 0 or args.limb_index > 8192:
            parser.error("--limb-index must be in 0..8192")
        if any(width < 1 or width > 63 for width in args.limb_widths):
            parser.error("--limb-widths must be in 1..63")
        print(
            json.dumps(
                limb_projection(
                    tuple(args.indices),
                    args.trials,
                    args.pattern,
                    tuple(dict.fromkeys(args.limb_widths)),
                    args.limb_index,
                ),
                indent=2,
            )
        )
        return 0
    if args.balanced_scaling:
        print(
            json.dumps(
                balanced_scaling(
                    args.family,
                    tuple(args.indices),
                    args.trials,
                    args.mode,
                    args.pattern,
                    args.mahler,
                ),
                indent=2,
            )
        )
        return 0
    result = run_probe()
    out = (
        report_directory("devtools.benchmarks.collatz_temporal_power_probe")
        / "collatz_temporal_power_metrics.json"
    )
    write_json_report(out, result)
    return 0


if __name__ == "__main__":
    raise SystemExit(run_reported(main))
