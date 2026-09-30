from __future__ import annotations

from devtools.benchmarks.reporting import write_markdown_json_report
from devtools.experiments.power_numbers.bounded_jump_profile import (
    markdown,
    metrics_dict,
)
from devtools.paths import report_directory, report_output, repository_root
from devtools.runs import run_reported

ROOT = repository_root()


def main() -> None:
    REPORT = report_output(
        "devtools.benchmarks.special_binary_jump_probe",
        "SPECIAL_BINARY_JUMP_RESULTS.md",
    )
    METRICS = (
        report_directory("devtools.benchmarks.special_binary_jump_probe")
        / "special_binary_jump_metrics.json"
    )
    report = markdown()
    metrics = metrics_dict()
    write_markdown_json_report(REPORT, METRICS, report, metrics)


if __name__ == "__main__":
    raise SystemExit(run_reported(main))
