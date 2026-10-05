"""Enforce current regressions corresponding to the historical adversarial audit.

The original results/action_morphism_adversarial_audit.json remains evidence of
past failures. This runner executes current regression assertions in fresh test
processes; failed, missing, or skipped cases cannot produce a passing report.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import UTC, datetime
from pathlib import Path
from uuid import uuid4

from devtools.checks.test_run_evidence import (
    minimal_selectors,
    validate_evidence,
)
from devtools.paths import repository_root
from number_compiler.resources.temporal_diagnostics import METRICS_SCHEMA_VERSION

ROOT = repository_root()
CASES = {
    "diamond_semantic_payloads": (
        "tests/hashlife/observation/test_diamond_payload_audit.py",
        "tests/arithmetic/contracts/test_diamond_metric_registry.py",
        "tests/hashlife/execution/test_diamond_geometry_payloads.py",
    ),
    "diamond_complete_kernels": (
        "tests/arithmetic/contracts/test_diamond_kernel.py",
        "tests/arithmetic/contracts/test_diamond_kernel_bridge.py",
    ),
    "diamond_scoped_actions": (
        "tests/arithmetic/contracts/test_diamond_actions.py",
        "tests/arithmetic/contracts/test_diamond_boundary.py",
    ),
    "diamond_midpoint_execution": (
        "tests/arithmetic/contracts/test_diamond_runtime.py",
        "tests/hashlife/execution/test_diamond_query.py",
        "tests/hashlife/interfaces/test_diamond_runtime_security.py",
    ),
    "diamond_parametric_macro_transfers": (
        "tests/arithmetic/contracts/test_diamond_pair_macros.py",
        "tests/hashlife/execution/test_diamond_primitive_pair.py",
    ),
    "certificate_binding": (
        "tests/arithmetic/contracts/test_certificate_binding_audit.py",
    ),
    "final_boundary_regressions": (
        "tests/arithmetic/contracts/test_final_boundary_audit.py",
    ),
    "source_handle_scope": (
        "tests/resources/test_recursive_field_images.py",
        "tests/resources/test_dyadic_return_audit.py::test_foreign_handle_with_equal_shape_is_not_local_authority",
        "tests/resources/test_dyadic_return_audit.py::test_audit_rejects_foreign_composite_source_authority",
    ),
    "application_dag_boundary": (
        "tests/arithmetic/contracts/test_application_dag_boundary.py",
    ),
    "reverse_dyadic_demand": ("tests/validation/proofs/test_reverse_dyadic_demand.py",),
    "collatz_dyadic_ranges": ("tests/resources/test_collatz_dyadic_ranges.py",),
    "measured_scaling_gate": ("tests/repository/test_lazy_scaling_audit.py",),
    "resource_metric_units": ("tests/projection/test_resource_metric_units.py",),
    "early_transfer_lookup": ("tests/validation/proofs/test_early_transfer_lookup.py",),
    "reverse_release_metric_units": (
        "tests/sequences/reverse_add/test_reverse_temporal_power_probe.py::test_reverse_release_probe_requires_measured_source_image_execution",
    ),
    "reverse_extensional_transfer_boundary": (
        "tests/validation/proofs/test_reverse_transfer_boundary.py",
    ),
    "proof_production_import_boundary": (
        "tests/repository/test_proof_production_boundary.py",
        "tests/validation/proofs/test_proof_oracle_boundary.py",
    ),
    "public_metrics": (
        "tests/sequences/reverse_add/test_reverse_temporal_power_probe.py::test_reverse_production_requires_exact_output_and_source_image_evidence",
        "tests/sequences/reverse_add/test_hashlife_behavior_growth.py::test_reverse_source_image_reports_exact_output_and_publications",
        "tests/hashlife/execution/test_hashlife_behavior_growth.py::test_action_metrics_report_image_publication_and_warm_response_reuse",
        "tests/validation/proofs/test_spacetime_cache_integrity.py::test_retained_cache_accounting_matches_independently_observed_containers",
        "tests/resources/test_lazy_reporting.py::test_forged_reservation_counts_fail_independent_reconciliation",
        "tests/resources/test_lazy_reporting.py::test_radix_registry_audits_actual_projection_and_rejects_hidden_payloads",
    ),
    "reverse_offsets": (
        "tests/sequences/reverse_add/test_lazy_reverse_public_audit.py::test_public_reverse_point_has_no_exact_future_carrier_or_global_offset_cache",
        "tests/resources/test_lazy_reporting.py::test_field_name_alone_cannot_disguise_an_unbounded_future_coefficient",
    ),
    "foreign_occurrence": (
        "tests/validation/proofs/reverse_add/test_reverse_occurrence_ownership.py::test_reverse_occurrence_foreign_owner_rejected_before_lookup",
        "tests/arithmetic/contracts/test_lazy_compiler_ownership.py::test_compiler_rejects_foreign_program_before_warm_or_zero_power",
        "tests/sequences/collatz/test_lazy_collatz_adversarial.py::test_collatz_foreign_view_rejected_for_point_summary_and_lowering",
    ),
    "operator_dispatch": (
        "tests/arithmetic/contracts/test_lazy_generic.py::test_generic_identity_then_normalization_is_two_without_family_inference",
        "tests/arithmetic/contracts/test_lazy_generic.py::test_custom_atom_cannot_alias_a_warm_supported_kernel_key",
    ),
    "kernel_identity": (
        "tests/arithmetic/contracts/test_lazy_generic.py::test_finite_kernel_identity_covers_frozen_behavior_and_ignores_names",
    ),
    "physical_fallback": (
        "tests/sequences/collatz/test_lazy_collatz_adversarial.py::test_public_collatz_point_and_width_never_lower_an_endpoint",
        "tests/resources/test_lazy_collatz.py::test_fixed_physical_cycle_and_even_prefix_do_not_expand_with_ticks",
    ),
    "adaptive_tail": (
        "tests/sequences/collatz/test_lazy_collatz_adversarial.py::test_large_valuation_keeps_only_finite_carries_and_symbolic_shifts",
        "tests/resources/test_lazy_collatz.py::test_long_zero_prefix_is_a_transfer_witness_not_an_integer_prefix",
    ),
    "symbolic_offset_lowering": (
        "tests/resources/test_lazy_reporting.py::test_payload_audit_detects_future_digits_and_unbounded_arithmetic",
        "tests/hashlife/execution/test_lowering_capability_poison.py::test_public_point_never_creates_lowering_capability",
        "tests/sequences/collatz/test_lazy_radix_adversarial.py",
    ),
    "budget_enforcement": (
        "tests/arithmetic/contracts/test_lazy_generic.py::test_zero_budget_rejects_before_source_geometry_or_branch_work",
        "tests/resources/test_resource_ledger.py::test_multi_owner_reservation_rejects_without_changing_peaks",
        "tests/resources/test_resource_ledger.py::test_container_identity_has_one_owner_and_same_owner_can_upgrade_resolver",
        "tests/resources/test_resource_ledger.py::test_disposed_owner_cannot_register_payloads_or_roots",
        "tests/resources/test_resource_ledger.py::test_dispose_releases_payload_and_rejects_even_warm_access",
        "tests/resources/test_resource_ledger.py::test_owning_term_and_ledger_lifetime_does_not_pin_unowned_arenas",
        "tests/resources/test_lazy_collatz.py::test_budget_reservation_is_preemptive_and_inventory_remains_consistent",
    ),
    "exact_tree_construction_boundary": (
        "tests/arithmetic/contracts/test_exact_tree_boundary.py",
    ),
    "independent_execution_ownership": ("tests/resources/test_resource_ownership.py",),
    "finite_kernel_snapshot": (
        "tests/arithmetic/automata/test_finite_kernel_snapshot.py",
    ),
    "oriented_action_lifetimes": (
        "tests/arithmetic/carry/test_oriented_action_ownership.py",
    ),
    "immutable_block_definitions": (
        "tests/arithmetic/contracts/test_block_definition.py",
    ),
    "execution_foundation": (
        "tests/arithmetic/contracts/test_execution_foundation_audit.py",
    ),
    "aggregate_numeric_payload": ("tests/resources/test_numeric_payload_aggregate.py",),
    "semantic_payload_domains": (
        "tests/validation/proofs/test_semantic_payload_barriers.py",
    ),
    "resource_store_boundaries": (
        "tests/arithmetic/contracts/test_resource_store_boundaries.py",
    ),
    "compiler_semantic_boundaries": (
        "tests/arithmetic/contracts/test_compiler_semantic_boundaries.py",
    ),
    "interleaved_metrics": (
        "tests/validation/proofs/test_spacetime_cache_integrity.py::test_metrics_do_not_attribute_other_indices_work_to_an_existing_index",
        "tests/sequences/reverse_add/test_lazy_reverse_public_audit.py::test_unrelated_public_reverse_query_cannot_change_existing_inventory_or_work",
    ),
}


def _case_result(
    name: str,
    required: tuple[str, ...],
    durations: dict[str, float],
    *,
    evidence: str,
    execution_reused: bool,
) -> dict[str, object]:
    selectors = CASES[name]
    nodes = tuple(
        node
        for node in required
        if any(
            node == selector or node.startswith((selector + "::", selector + "["))
            for selector in selectors
        )
    )
    if not nodes:
        raise ValueError(f"no current test nodes cover audit case {name}")
    return {
        "status": "PASS",
        "tests": len(nodes),
        "selectors": selectors,
        "seconds": sum(durations[node] for node in nodes),
        "errors_failures_skips": 0,
        "evidence": evidence,
        "execution_reused": execution_reused,
    }


def run_cases(names: tuple[str, ...]) -> dict[str, dict[str, object]]:
    """Execute the union once, then attribute validated nodes to each case."""
    selectors = tuple(
        dict.fromkeys(selector for name in names for selector in CASES[name])
    )
    run_parent = ROOT / "results" / "runs"
    run_parent.mkdir(parents=True, exist_ok=True)
    run_directory = run_parent / (
        datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ") + "-morphism-" + uuid4().hex
    )
    command = [
        sys.executable,
        "-m",
        "devtools.checks.release",
        "--suite",
        "unit",
        "--output-dir",
        str(run_directory),
    ]
    for selector in minimal_selectors(selectors):
        command.extend(("--select", selector))
    completed = subprocess.run(
        command,
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    report = run_directory / "unit.xml"
    if completed.returncode != 0 or not report.exists():
        raise RuntimeError(
            "adversarial regression union failed:\n"
            f"{completed.stdout}\n{completed.stderr}"
        )
    durations = validate_evidence(
        report,
        ROOT,
        require_clean=False,
        require_acceptance=False,
    )
    required = tuple(durations)
    for selector in selectors:
        if not any(
            node == selector or node.startswith((selector + "::", selector + "["))
            for node in required
        ):
            raise ValueError(f"guarded run omitted requested selector {selector}")
    return {
        name: _case_result(
            name,
            required,
            durations,
            evidence=str(report),
            execution_reused=False,
        )
        for name in names
    }


def run_case(name: str) -> dict[str, object]:
    """Compatibility entry point for one explicitly selected audit case."""
    return run_cases((name,))[name]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=sorted(CASES))
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--junit",
        type=Path,
        help="reuse a complete passing run with matching source and test manifests",
    )
    args = parser.parse_args()
    protected = {
        (ROOT / "results/action_morphism_adversarial_audit.json").resolve(),
        (ROOT / "results/action_morphism_adversarial_validation_v2.json").resolve(),
        (ROOT / "results/followup_representation_audit_v3.json").resolve(),
        (ROOT / "results/followup_representation_audit_v4.json").resolve(),
        (ROOT / "results/followup_representation_audit_v5.json").resolve(),
        (ROOT / "results/followup_representation_audit_v6.json").resolve(),
    }
    if args.output is not None and args.output.resolve() in protected:
        parser.error(
            "historical counterexamples and prior validation must not be overwritten"
        )
    expensive = ("reverse_release_metric_units", "symbolic_offset_lowering")
    names = (
        (args.case,)
        if args.case is not None
        else (*tuple(name for name in CASES if name not in expensive), *expensive)
    )
    if args.junit is None:
        checks = run_cases(names)
    else:
        selectors = tuple(
            dict.fromkeys(selector for name in names for selector in CASES[name])
        )
        durations = validate_evidence(
            args.junit,
            ROOT,
            require_clean=True,
            require_acceptance=True,
        )
        required = tuple(durations)
        if any(
            not any(
                node == selector or node.startswith((selector + "::", selector + "["))
                for node in required
            )
            for selector in selectors
        ):
            parser.error("reused JUnit evidence omits a requested audit selector")
        checks = {
            name: _case_result(
                name,
                required,
                durations,
                evidence=str(args.junit),
                execution_reused=True,
            )
            for name in names
        }
    result = {
        "metrics_schema_version": METRICS_SCHEMA_VERSION,
        "audit_revision": 8,
        "prior_validation": "results/followup_representation_audit_v6.json",
        "historical_counterexamples": "results/action_morphism_adversarial_audit.json",
        "status_scope": "Regression assertions only; measured scaling acceptance is reported separately.",
        "performance_gate_artifact": "results/lazy_resource_audit_v7.json",
        "status": "PASS",
        "checks": checks,
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
