"""Emit v0.52.8 metrics for special-number idempotent output quotients."""

from __future__ import annotations

from devtools.paths import report_directory

import json
from dataclasses import asdict

from devtools.experiments.power_numbers.special_idempotent_output import (
    boolean_output_quotient_audit,
    mixed_split_endpoint_counterexample_audit,
    output_partition_successor_closure_audit,
    rank_two_quadratic_power_audit,
    raw_special_materialization_audit,
    terminal_idempotent_control_audit,
)
from devtools.paths import repository_root

ROOT = repository_root()

CONTROLS = (
    ("fermat", 4),
    ("fermat", 5),
    ("mersenne", 11),
    ("mersenne", 13),
)
POWER_CONTROLS = (
    ("fermat", 4, 7),
    ("fermat", 5, 5),
    ("mersenne", 11, 8),
    ("mersenne", 13, 10),
)


def main() -> None:
    payload = {
        "version": "0.52.8",
        "controls": [
            asdict(terminal_idempotent_control_audit(*row)) for row in CONTROLS
        ],
        "mixed_m29": asdict(mixed_split_endpoint_counterexample_audit()),
        "successor_closure": asdict(output_partition_successor_closure_audit()),
        "raw_independence": [
            asdict(raw_special_materialization_audit(*row)) for row in CONTROLS
        ],
        "rank_two_power": [
            asdict(rank_two_quadratic_power_audit(*row)) for row in POWER_CONTROLS
        ],
        "output_examples": {
            "collapsed": asdict(boolean_output_quotient_audit((False, True), (3, 3))),
            "separating": asdict(boolean_output_quotient_audit((False, True), (3, 7))),
            "rejected": asdict(
                boolean_output_quotient_audit((False, False, True), (3, 4, 7))
            ),
        },
    }
    out = (
        report_directory("devtools.benchmarks.special_idempotent_output_probe")
        / "special_idempotent_output_metrics.json"
    )
    text = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    out.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
