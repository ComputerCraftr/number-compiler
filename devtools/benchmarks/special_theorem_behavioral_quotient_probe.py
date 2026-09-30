from __future__ import annotations

import json
from dataclasses import asdict

from devtools.experiments.power_numbers.special_theorem_behavioral_quotient import (
    theorem_behavioral_frontier,
    theorem_behavioral_quotient_audit,
    two_primary_depth_comparison,
)
from devtools.paths import report_output


def main() -> None:
    controls = [
        theorem_behavioral_quotient_audit("fermat", 2),
        theorem_behavioral_quotient_audit("fermat", 3),
        theorem_behavioral_quotient_audit("fermat", 4),
        theorem_behavioral_quotient_audit("mersenne", 5),
        theorem_behavioral_quotient_audit("mersenne", 7),
        theorem_behavioral_quotient_audit("mersenne", 11),
        theorem_behavioral_quotient_audit("mersenne", 13),
    ]
    data = {
        "controls": [asdict(row) for row in controls],
        "two_primary_comparisons": [
            asdict(two_primary_depth_comparison("fermat", 4)),
            asdict(two_primary_depth_comparison("mersenne", 13)),
        ],
        "frontier": asdict(theorem_behavioral_frontier()),
    }
    text = json.dumps(data, indent=2, sort_keys=True) + "\n"
    out = report_output(
        "devtools.benchmarks.special_theorem_behavioral_quotient_probe",
        "special_theorem_behavioral_quotient_metrics.json",
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
