"""Release-facing metrics for the shared Fermat/Mersenne terminal threshold."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path

from devtools.experiments.algebra.dyadic_difference_germ_terminal import (
    fermat_filtration_requirement_audit,
    fermat_sparse_candidate_quotient_audit,
    mersenne_filtration_requirement_audit,
    mersenne_sparse_candidate_quotient_audit,
    mersenne_sparse_torus_base_change_audit,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    terminal_threshold_probe,
    terminal_threshold_spec,
)


def report() -> dict[str, object]:
    cases = (("fermat", 4), ("fermat", 5), ("mersenne", 11), ("mersenne", 13))
    specs = [terminal_threshold_spec(family, parameter) for family, parameter in cases]
    probes = [
        terminal_threshold_probe(family, parameter) for family, parameter in cases
    ]
    f4 = fermat_filtration_requirement_audit(4)
    f5 = fermat_filtration_requirement_audit(5)
    m11 = mersenne_filtration_requirement_audit(11)
    m13 = mersenne_filtration_requirement_audit(13)
    fq = fermat_sparse_candidate_quotient_audit(4)
    mq = mersenne_sparse_candidate_quotient_audit(13)
    mt = mersenne_sparse_torus_base_change_audit(13)
    return {
        "terminal_specs": [asdict(row) for row in specs],
        "terminal_probes": [asdict(row) for row in probes],
        "fermat_audits": [asdict(f4), asdict(f5)],
        "mersenne_audits": [asdict(m11), asdict(m13)],
        "sparse_quotients": {
            "fermat_f4_exact": fq.exact,
            "mersenne_m13_exact": mq.exact,
            "mersenne_torus_base_change_exact": mt.exact,
        },
        "invariants": {
            "one_terminal_boolean_suffices_for_prime_decision": all(
                row.pass_iff_prime for row in specs
            ),
            "fermat_terminal_formula": tuple(row.terminal_level for row in specs[:2])
            == (11, 26),
            "mersenne_terminal_formula": tuple(row.terminal_level for row in specs[2:])
            == (9, 11),
            "prime_pass_reconstructs_pure_filtration": f4.bounded_reference_matches_pure_theorem
            is True
            and m13.bounded_reference_matches_pure_theorem is True,
            "composite_exact_residual_is_optional_stronger_problem": f4.full_histogram_required_for_exact_composite_residual
            and f5.full_histogram_required_for_exact_composite_residual
            and m11.full_histogram_required_for_exact_composite_residual
            and m13.full_histogram_required_for_exact_composite_residual,
            "terminal_selector_still_unavailable_on_release_controls": all(
                row.status == "UNKNOWN" for row in probes
            ),
            "no_probe_carrier_enumeration": all(
                row.carrier_states_enumerated == 0 for row in probes
            ),
            "no_probe_recurrence_replay": all(
                row.raw_specialization_squarings == 0 for row in probes
            ),
        },
        "remaining_blocker": "locality-preserving terminal Kummer/Artin support selector",
    }


def main() -> None:
    payload = report()
    out = Path("results/special_terminal_threshold_metrics.json")
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
