"""Measure bounded temporal semantics separately from spatial application growth.

The HashLife root is the literal seed.  The powered operator is reusable temporal
semantics.  Concrete recursive boundary/residual objects created while applying
that operator are spatial occurrence/cache objects and are reported separately.

For M(N), ``local_exponent = log(M(N)/M(N/2))/log(2)`` on the default doubling
schedule.  Values below one are sublinear in generation count.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from itertools import pairwise
from math import log, log2

from devtools.checks.lazy_scaling_audit import (
    SPACE_METRICS,
    WORK_METRICS,
    assess_series,
)
from number_compiler.resources.metric_collection import ledger_fields_from
from number_compiler.resources.metric_records import LedgerMetrics
from number_compiler.resources.metric_replace import replace_metric
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


@dataclass(frozen=True, slots=True)
class GrowthRow(LedgerMetrics):
    generation: int
    exact_output_width: int
    max_prefix_output_width: int
    logical_width_bound: int
    seed_payload_tile_nodes: int
    padded_root_tile_nodes: int
    retained_spatial_tile_nodes: int
    application_spatial_tile_nodes: int
    powered_operator_nodes: int
    temporal_quotient_family: str
    temporal_quotient_horizon: int
    temporal_cell_payload_bits: int
    temporal_residue_prime: int
    temporal_residue_precision: int
    temporal_residue_classes: int
    temporal_symbolic_exponent_fields: int
    temporal_quotient_state_class_bound: int
    temporal_quotient_action_class_bound: int
    temporal_local_action_class_bound: int
    temporal_quotient_descriptor_bits_bound: int
    temporal_cocycle_weight_fields: int
    compiler_temporal_state_nodes: int
    compiler_temporal_action_nodes: int
    compiler_recursive_state_action_shared_nodes: int
    temporal_description_nodes: int
    seed_application_temporal_state_nodes: int
    seed_application_temporal_action_nodes: int
    seed_application_temporal_description_nodes: int
    spatial_occurrence_state_nodes: int
    spatial_occurrence_action_nodes: int
    spatial_occurrence_recursive_state_action_shared_nodes: int
    spatial_occurrence_description_nodes: int
    unquotiented_recursive_application_state_nodes: int
    unquotiented_recursive_application_action_nodes: int
    unquotiented_recursive_application_description_nodes: int
    runtime_image_matches_oracle: bool
    runtime_replay_publications_stable: bool
    runtime_source_image_publications: int
    runtime_completed_result_publications: int
    execution_memo_entries: int
    retained_effect_memo_entries: int
    recursive_spatial_residual_max_extent: int
    recursive_spatial_residual_max_depth: int
    recursive_boundary_wrapper_nodes: int
    spatial_occurrence_accounting_delta: int
    raw_temporal_scalar_length_fields: int
    raw_temporal_span_fields: int
    raw_spatial_occurrence_scalar_extent_fields: int
    eager_spatial_observer_fields: int
    bounded_application_exact_spatial_occurrences: int
    bounded_application_symbolic_action_nodes: int
    bounded_application_jump_entries: int
    bounded_application_primitive_step_evaluations: int
    bounded_application_action_compositions: int
    bounded_application_action_applications: int
    bounded_application_nonlinear_branch_evaluations: int
    bounded_application_exact_endpoint_entries: int
    bounded_application_residual_physical_steps: int
    temporal_nodes_per_log2_generation: float
    seed_application_temporal_nodes_per_generation: float
    spatial_occurrence_nodes_per_generation: float
    spatial_occurrence_nodes_per_output_digit: float
    temporal_local_exponent: float | None
    seed_application_temporal_local_exponent: float | None
    spatial_occurrence_local_exponent: float | None
    spatial_tile_local_exponent: float | None
    primitive_step_local_exponent: float | None
    memo_local_exponent: float | None


def _digit_width(value: int, base: int) -> int:
    value, base = int(value), int(base)
    if value == 0:
        return 1
    width = 0
    while value:
        value //= base
        width += 1
    return width


def _reverse_in_base(value: int, base: int) -> int:
    digits: list[int] = []
    if value == 0:
        return 0
    while value:
        value, digit = divmod(value, base)
        digits.append(digit)
    out = 0
    place = 1
    for digit in reversed(digits):
        out += digit * place
        place *= base
    return out


def _reverse_widths(seed: int, generation: int, base: int) -> tuple[int, int]:
    value = int(seed)
    peak = _digit_width(value, base)
    for _ in range(int(generation)):
        value += _reverse_in_base(value, base)
        peak = max(peak, _digit_width(value, base))
    return _digit_width(value, base), peak


def _reverse_value(seed: int, generation: int, base: int) -> int:
    value = int(seed)
    for _ in range(int(generation)):
        value += _reverse_in_base(value, base)
    return value


def _collatz_widths(seed: int, generation: int) -> tuple[int, int]:
    value = int(seed)
    peak = max(1, value.bit_length())
    for _ in range(int(generation)):
        value = 3 * value + 1 if value & 1 else value // 2
        peak = max(peak, max(1, value.bit_length()))
    return max(1, value.bit_length()), peak


def _collatz_value(seed: int, generation: int) -> int:
    value = int(seed)
    for _ in range(int(generation)):
        value = 3 * value + 1 if value & 1 else value // 2
    return value


def _local_exponent(
    previous_n: int, previous_value: int, n: int, value: int
) -> float | None:
    if min(previous_n, previous_value, n, value) <= 0 or n <= previous_n:
        return None
    return log(value / previous_value) / log(n / previous_n)


def _build_rows(
    family: str, seed: int, generations: tuple[int, ...], *, base: int
) -> list[GrowthRow]:
    rows: list[GrowthRow] = []
    previous: GrowthRow | None = None
    for generation in generations:
        term: PoweredCollatzTerm | ReverseAddPoweredTerm
        if family == "reverse":
            term = ReverseAddPoweredTerm(seed, generation, base=base)
            exact_width, peak_width = _reverse_widths(seed, generation, base)
        else:
            term = PoweredCollatzTerm(seed, generation)
            exact_width, peak_width = _collatz_widths(seed, generation)

        # Compare one public output point with an independent scalar oracle.
        expected_output = (
            _reverse_value(seed, generation, base)
            if family == "reverse"
            else _collatz_value(seed, generation)
        )
        expected_low = (
            expected_output % base if family == "reverse" else expected_output & 1
        )
        observed_low = term.digit(0)
        if observed_low != expected_low:
            raise AssertionError((family, seed, generation, observed_low, expected_low))
        before_replay = dict(term.resource_ledger.counters)
        if term.digit(0) != observed_low:
            raise AssertionError(("runtime-image-replay-mismatch", family, generation))
        after_replay = term.resource_ledger.counters
        m = term.behavior_metrics()
        replay_publications_stable = after_replay.get(
            "source_image_publications", 0
        ) == before_replay.get("source_image_publications", 0) and after_replay.get(
            "completed_result_publications", 0
        ) == before_replay.get("completed_result_publications", 0)
        spatial_occ = m.spatial_occurrence_description_nodes
        row = GrowthRow(
            generation=generation,
            exact_output_width=exact_width,
            max_prefix_output_width=peak_width,
            logical_width_bound=m.logical_width_bound,
            seed_payload_tile_nodes=m.seed_payload_tile_nodes,
            padded_root_tile_nodes=m.padded_root_tile_nodes,
            retained_spatial_tile_nodes=m.retained_spatial_tile_nodes,
            application_spatial_tile_nodes=m.application_spatial_tile_nodes,
            powered_operator_nodes=m.powered_operator_nodes,
            temporal_quotient_family=m.temporal_quotient_family,
            temporal_quotient_horizon=m.temporal_quotient_horizon,
            temporal_cell_payload_bits=m.temporal_cell_payload_bits,
            temporal_residue_prime=m.temporal_residue_prime,
            temporal_residue_precision=m.temporal_residue_precision,
            temporal_residue_classes=m.temporal_residue_classes,
            temporal_symbolic_exponent_fields=m.temporal_symbolic_exponent_fields,
            temporal_quotient_state_class_bound=m.temporal_quotient_state_class_bound,
            temporal_quotient_action_class_bound=m.temporal_quotient_action_class_bound,
            temporal_local_action_class_bound=m.temporal_local_action_class_bound,
            temporal_quotient_descriptor_bits_bound=m.temporal_quotient_descriptor_bits_bound,
            temporal_cocycle_weight_fields=m.temporal_cocycle_weight_fields,
            compiler_temporal_state_nodes=m.compiler_temporal_state_nodes,
            compiler_temporal_action_nodes=m.compiler_temporal_action_nodes,
            compiler_recursive_state_action_shared_nodes=m.compiler_recursive_state_action_shared_nodes,
            temporal_description_nodes=m.temporal_description_nodes,
            seed_application_temporal_state_nodes=m.seed_application_temporal_state_nodes,
            seed_application_temporal_action_nodes=m.seed_application_temporal_action_nodes,
            seed_application_temporal_description_nodes=m.seed_application_temporal_description_nodes,
            spatial_occurrence_state_nodes=m.spatial_occurrence_state_nodes,
            spatial_occurrence_action_nodes=m.spatial_occurrence_action_nodes,
            spatial_occurrence_recursive_state_action_shared_nodes=m.spatial_occurrence_recursive_state_action_shared_nodes,
            spatial_occurrence_description_nodes=spatial_occ,
            unquotiented_recursive_application_state_nodes=m.unquotiented_recursive_application_state_nodes,
            unquotiented_recursive_application_action_nodes=m.unquotiented_recursive_application_action_nodes,
            unquotiented_recursive_application_description_nodes=m.unquotiented_recursive_application_description_nodes,
            runtime_image_matches_oracle=observed_low == expected_low,
            runtime_replay_publications_stable=replay_publications_stable,
            runtime_source_image_publications=(
                m.temporal_diagnostics.construction.source_image_publications or 0
            ),
            runtime_completed_result_publications=m.completed_result_publications,
            execution_memo_entries=m.execution_memo_entries,
            retained_effect_memo_entries=m.retained_effect_memo_entries,
            recursive_spatial_residual_max_extent=m.recursive_spatial_residual_max_extent,
            recursive_spatial_residual_max_depth=m.recursive_spatial_residual_max_depth,
            recursive_boundary_wrapper_nodes=m.recursive_boundary_wrapper_nodes,
            spatial_occurrence_accounting_delta=m.spatial_occurrence_accounting_delta,
            raw_temporal_scalar_length_fields=m.raw_temporal_scalar_length_fields,
            raw_temporal_span_fields=m.raw_temporal_span_fields,
            raw_spatial_occurrence_scalar_extent_fields=m.raw_spatial_occurrence_scalar_extent_fields,
            eager_spatial_observer_fields=m.eager_spatial_observer_fields,
            bounded_application_exact_spatial_occurrences=m.bounded_application_exact_spatial_occurrences,
            bounded_application_symbolic_action_nodes=m.bounded_application_symbolic_action_nodes,
            bounded_application_jump_entries=m.bounded_application_jump_entries,
            bounded_application_primitive_step_evaluations=m.bounded_application_primitive_step_evaluations,
            bounded_application_action_compositions=m.bounded_application_action_compositions,
            bounded_application_action_applications=m.bounded_application_action_applications,
            bounded_application_nonlinear_branch_evaluations=m.bounded_application_nonlinear_branch_evaluations,
            bounded_application_exact_endpoint_entries=m.bounded_application_exact_endpoint_entries,
            bounded_application_residual_physical_steps=m.bounded_application_residual_physical_steps,
            temporal_nodes_per_log2_generation=(
                m.temporal_description_nodes / max(1.0, log2(generation))
            ),
            seed_application_temporal_nodes_per_generation=(
                m.seed_application_temporal_description_nodes / generation
            ),
            spatial_occurrence_nodes_per_generation=spatial_occ / generation,
            spatial_occurrence_nodes_per_output_digit=spatial_occ / exact_width,
            temporal_local_exponent=None
            if previous is None
            else _local_exponent(
                previous.generation,
                previous.temporal_description_nodes,
                generation,
                m.temporal_description_nodes,
            ),
            seed_application_temporal_local_exponent=None
            if previous is None
            else _local_exponent(
                previous.generation,
                previous.seed_application_temporal_description_nodes,
                generation,
                m.seed_application_temporal_description_nodes,
            ),
            spatial_occurrence_local_exponent=None
            if previous is None
            else _local_exponent(
                previous.generation,
                previous.spatial_occurrence_description_nodes,
                generation,
                spatial_occ,
            ),
            spatial_tile_local_exponent=None
            if previous is None
            else _local_exponent(
                previous.generation,
                previous.application_spatial_tile_nodes,
                generation,
                m.application_spatial_tile_nodes,
            ),
            primitive_step_local_exponent=None
            if previous is None
            else _local_exponent(
                previous.generation,
                previous.bounded_application_primitive_step_evaluations,
                generation,
                m.bounded_application_primitive_step_evaluations,
            ),
            memo_local_exponent=None
            if previous is None
            else _local_exponent(
                previous.generation,
                previous.execution_memo_entries,
                generation,
                m.execution_memo_entries,
            ),
        )
        row = replace_metric(row, ledger_fields_from(m))
        rows.append(row)
        previous = row
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("family", choices=("reverse", "collatz"))
    parser.add_argument("seed", type=int)
    parser.add_argument("--generations", default="16,32,64,128,256")
    parser.add_argument("--base", type=int, default=10)
    args = parser.parse_args()
    generations = tuple(int(x) for x in args.generations.split(",") if x.strip())
    if not generations or any(x <= 0 for x in generations):
        raise SystemExit("generations must be positive")
    if any(b <= a for a, b in pairwise(generations)):
        raise SystemExit("generations must be strictly increasing")

    rows = _build_rows(args.family, args.seed, generations, base=args.base)
    tail = rows[-1]
    measured = (
        {
            name: assess_series(generations, [getattr(row, name) for row in rows])
            for name in (*SPACE_METRICS, *WORK_METRICS)
        }
        if len(rows) > 1
        else {}
    )
    for name in sorted(set().union(*(row.resource_work_counters for row in rows))):
        if len(rows) > 1:
            measured["work." + name] = assess_series(
                generations, [row.resource_work_counters.get(name, 0) for row in rows]
            )
    payload = {
        "family": args.family,
        "seed": args.seed,
        "base": args.base if args.family == "reverse" else 2,
        "metric_contract": {
            "seed_payload_is_generation_independent": len(
                {r.seed_payload_tile_nodes for r in rows}
            )
            == 1,
            "seed_application_local_state_nodes_are_bounded": all(
                r.seed_application_temporal_state_nodes
                <= r.temporal_local_action_class_bound
                for r in rows
            ),
            "raw_temporal_scalar_length_fields_are_zero": all(
                r.raw_temporal_scalar_length_fields == 0 for r in rows
            ),
            "raw_temporal_span_fields_are_zero": all(
                r.raw_temporal_span_fields == 0 for r in rows
            ),
            "raw_spatial_occurrence_scalar_extent_fields_are_zero": all(
                r.raw_spatial_occurrence_scalar_extent_fields == 0 for r in rows
            ),
            "eager_spatial_observer_fields_are_zero": all(
                r.eager_spatial_observer_fields == 0 for r in rows
            ),
            "temporal_quotient_class_bounds_are_generation_independent": (
                len({r.temporal_quotient_state_class_bound for r in rows}) == 1
                and len({r.temporal_quotient_action_class_bound for r in rows}) == 1
            ),
            "recursive_boundary_wrapper_nodes_are_zero": all(
                r.recursive_boundary_wrapper_nodes == 0 for r in rows
            ),
            "spatial_occurrence_accounting_is_exact": all(
                r.resource_audit_complete == 1 and r.resource_accounting_mismatch == 0
                for r in rows
            ),
            "retained_payload_audit_passes": all(
                r.resource_audit_complete == 1
                and r.forbidden_future_payloads == 0
                and r.retained_unbounded_future_integers == 0
                for r in rows
            ),
            "temporal_vs_spatial_occurrence_split": all(
                r.spatial_occurrence_description_nodes
                == r.spatial_binding_nodes + r.canonical_transfer_nodes
                and r.seed_application_temporal_description_nodes
                == r.application_program_nodes
                and r.cache_slots == r.resource_observed_entries
                for r in rows
            ),
            "symbolic_action_closure_has_no_fixed_finite_bound": all(
                r.temporal_quotient_action_class_bound == 0 for r in rows
            ),
            "primitive_branch_work_is_reported_separately": all(
                r.bounded_application_primitive_step_evaluations
                >= r.bounded_application_nonlinear_branch_evaluations
                for r in rows
            ),
            "runtime_image_publication_contract_passes": all(
                r.runtime_image_matches_oracle
                and r.runtime_replay_publications_stable
                and r.resource_audit_complete == 1
                and r.resource_accounting_mismatch == 0
                and (
                    r.runtime_source_image_publications > 0
                    if r.temporal_quotient_family == "collatz-dyadic-source-image"
                    else r.runtime_completed_result_publications > 0
                )
                for r in rows
            ),
            "unquotiented_recursive_application_nodes_are_zero": all(
                r.unquotiented_recursive_application_description_nodes == 0
                for r in rows
            ),
            "sublinear_threshold": "local_exponent < 1",
            "output_width_source": "independent scalar oracle; does not mutate HashLife caches",
        },
        "rows": [asdict(row) for row in rows],
        "measured_cold_resource_growth": measured,
        "warm_work_measured": False,
        "tail": {
            "generation": tail.generation,
            "temporal_local_exponent": tail.temporal_local_exponent,
            "spatial_occurrence_local_exponent": tail.spatial_occurrence_local_exponent,
            "spatial_tile_local_exponent": tail.spatial_tile_local_exponent,
            "memo_local_exponent": tail.memo_local_exponent,
            "temporal_description_sublinear": (
                tail.temporal_local_exponent is not None
                and tail.temporal_local_exponent < 1.0
            ),
            "seed_application_temporal_description_sublinear": (
                tail.seed_application_temporal_local_exponent is not None
                and tail.seed_application_temporal_local_exponent < 1.0
            ),
            "spatial_occurrence_description_sublinear": (
                tail.spatial_occurrence_local_exponent is not None
                and tail.spatial_occurrence_local_exponent < 1.0
            ),
            "remaining_execution_scaling_blocker": (
                not measured
                or any(metric["status"] != "PASS" for metric in measured.values())
            ),
        },
    }
    print(json.dumps(payload, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
