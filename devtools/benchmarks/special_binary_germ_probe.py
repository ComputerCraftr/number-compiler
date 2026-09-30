"""Emit metrics for the binary Fermat/Mersenne support-germ checkpoint."""

from __future__ import annotations

from devtools.paths import report_directory


from devtools.experiments.power_numbers.special_binary_germ import (
    special_binary_germ_truth_audit,
)
from devtools.paths import repository_root
from devtools.benchmarks.reporting import write_json_report
from number_compiler.sequences.power_numbers.germ import build_special_germ_plan
from number_compiler.sequences.power_numbers.terminal_threshold import (
    prime_decision_chunk_spec,
    terminal_threshold_spec,
)

ROOT = repository_root()


def main() -> None:
    rows = []
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        spec = prime_decision_chunk_spec(terminal_threshold_spec(family, parameter))
        plan = build_special_germ_plan(spec)
        truth = special_binary_germ_truth_audit(family, parameter)
        rows.append(
            {
                "family": family,
                "parameter": parameter,
                "start_level": spec.start_level,
                "span": spec.span,
                "endpoint_level": spec.end_level,
                "binary_compositions": plan.binary_compositions,
                "support_observations": plan.support_observations,
                "one_level_replays": plan.one_level_replays,
                "factor_enumeration_production": plan.factor_enumeration,
                "truth_status": truth.endpoint_result.status,
                "truth_composition_exact": truth.exact,
                "factor_enumeration_audit": truth.factor_enumeration,
            }
        )
    payload = {
        "theorem_status": "SOURCE_OBSERVER_UNKNOWN",
        "binary_transport_closed": True,
        "support_intersection_closed": True,
        "candidate_support_extractor_available": False,
        "rows": rows,
    }
    out = (
        report_directory("devtools.benchmarks.special_binary_germ_probe")
        / "special_binary_germ_metrics.json"
    )
    write_json_report(out, payload)


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
