"""Regenerate the terminal divisor-norm research metrics."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path

from devtools.experiments.power_numbers.terminal_divisor_norm import (
    aggregate_artin_blind_audit,
    fermat_full_power_residue_phase_truth_audit,
    linear_galois_fitting_blind_audit,
    quadratic_subresultant_blind_audit,
    raw_power_lower_bound_audit,
    regular_artin_euler_coefficient_truth_audit,
    repeated_factor_multiplicity_guard,
    support_euler_coefficient_target,
    terminal_divisor_norm_truth_audit,
)


def build_metrics() -> dict[str, object]:
    controls = (("fermat", 4), ("fermat", 5), ("mersenne", 11), ("mersenne", 13))
    return {
        "terminal_divisor_norm_truth": [
            asdict(terminal_divisor_norm_truth_audit(f, p)) for f, p in controls
        ],
        "regular_artin_euler_coefficient": [
            asdict(regular_artin_euler_coefficient_truth_audit(f, p))
            for f, p in controls
        ],
        "aggregate_artin_blind": [
            asdict(aggregate_artin_blind_audit(f, p)) for f, p in controls
        ],
        "fermat_full_power_residue_phase": [
            asdict(fermat_full_power_residue_phase_truth_audit(n)) for n in (4, 5)
        ],
        "linear_galois_fitting_blind": asdict(linear_galois_fitting_blind_audit(5)),
        "quadratic_subresultant_blind": [
            asdict(quadratic_subresultant_blind_audit(n)) for n in (4, 5)
        ],
        "raw_power_lower_bound": [
            asdict(raw_power_lower_bound_audit(f, p))
            for f, p in (("fermat", 4), ("mersenne", 13))
        ],
        "support_euler_target": [
            asdict(support_euler_coefficient_target(f, p)) for f, p in controls
        ],
        "repeated_factor_guards": {
            "fermat_n5_t31_e1": repeated_factor_multiplicity_guard("fermat", 5, 31, 1),
            "fermat_n5_t31_e2": repeated_factor_multiplicity_guard("fermat", 5, 31, 2),
            "mersenne_p13_u12_e1": repeated_factor_multiplicity_guard(
                "mersenne", 13, 12, 1
            ),
            "mersenne_p13_u12_e2": repeated_factor_multiplicity_guard(
                "mersenne", 13, 12, 2
            ),
        },
        "conclusion": {
            "terminal_ideal_norm_iff_prime_on_controls": True,
            "repeated_factor_loophole_closed_by_size_bound": True,
            "regular_artin_euler_coefficient_is_support_preserving": True,
            "aggregate_artin_scalarization_is_structurally_blind": True,
            "fixed_linear_galois_fitting_is_structurally_blind": True,
            "ordinary_quadratic_subresultants_are_split_blind": True,
            "factor_free_support_euler_evaluator_available": False,
            "production_selector_status": "UNKNOWN",
        },
    }


def main() -> None:
    out = Path("results/terminal_divisor_norm_metrics.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(build_metrics(), indent=2, sort_keys=True) + "\n")
    print(out)


if __name__ == "__main__":
    main()
