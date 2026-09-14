from __future__ import annotations

import json

from devtools.experiments.power_numbers.bounded_jump_profile import (
    markdown,
    metrics_dict,
)
from devtools.paths import report_output, repository_root

ROOT = repository_root()

REPORT = report_output(
    "devtools.benchmarks.special_binary_jump_probe", "SPECIAL_BINARY_JUMP_RESULTS.md"
)
METRICS = ROOT / "results" / "special_binary_jump_metrics.json"


def main() -> None:
    report = markdown()
    metrics = metrics_dict()
    REPORT.write_text(report)
    METRICS.parent.mkdir(parents=True, exist_ok=True)
    METRICS.write_text(json.dumps(metrics, indent=2, sort_keys=True) + "\n")
    print(report, end="")


if __name__ == "__main__":
    main()
