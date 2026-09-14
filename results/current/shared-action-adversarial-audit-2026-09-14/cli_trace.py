"""Bounded CLI call traces; instrumentation is not a latency benchmark."""

from __future__ import annotations

import io
import json
from collections import Counter
from contextlib import redirect_stderr, redirect_stdout
from unittest.mock import patch

from number_compiler.api import cli
from number_compiler.api.number_api import NumberCompiler
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundSchedulerCore,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def trace(arguments: list[str]) -> dict[str, object]:
    counts: Counter[str] = Counter()
    owners: list[AntihydraArithmeticTerm] = []
    apply = SourceBoundSchedulerCore.apply
    validate = AntihydraArithmeticTerm._validate_result
    result = AntihydraArithmeticTerm.result

    def traced_apply(self, adapter, source, action):
        counts[f"shared_apply:{adapter.family}"] += 1
        return apply(self, adapter, source, action)

    def traced_validate(self, value):
        counts["antihydra_result_validation_calls"] += 1
        return validate(self, value)

    def traced_result(self):
        counts["antihydra_result_requests"] += 1
        if all(self is not owner for owner in owners):
            owners.append(self)
        return result(self)

    out, err = io.StringIO(), io.StringIO()
    NumberCompiler().clear_shared_cache()
    with (
        patch.object(SourceBoundSchedulerCore, "apply", traced_apply),
        patch.object(AntihydraArithmeticTerm, "_validate_result", traced_validate),
        patch.object(AntihydraArithmeticTerm, "result", traced_result),
        redirect_stdout(out),
        redirect_stderr(err),
    ):
        status = cli.main(arguments + ["--format", "json"])
    packet = json.loads(out.getvalue()) if out.getvalue().strip() else None
    return {
        "arguments": arguments,
        "exit_code": status,
        "stderr": err.getvalue(),
        "calls": dict(counts),
        "antihydra_owner_count": len(owners),
        "antihydra_final_counters": [dict(owner.ledger.counters) for owner in owners],
        "packet": packet,
    }


def main() -> None:
    requests = [
        ["prime", "--nth", "100", "--info", "metrics"],
        ["196", "--nth", "4"],
        ["collatz", "--nth", "4", "--seed", "27", "--info", "clock"],
        ["collatz", "--events", "4", "--seed", "27", "--info", "modular"],
        ["fermat", "--nth", "4", "--no-value", "--info", "primality"],
        ["mersenne", "--nth", "11", "--no-value", "--info", "factor"],
    ]
    for n in (64, 128, 256):
        for names in (
            ("clock",),
            ("clock", "clock"),
            ("clock", "tape"),
            ("clock", "tape", "hasse"),
            ("spacetime",),
        ):
            arguments = ["antihydra", "--nth", str(n), "--no-value"]
            for name in names:
                arguments.extend(("--info", name))
            requests.append(arguments)
            if names == ("spacetime",):
                requests.append(arguments + ["--modulus", "3"])
    rows = [trace(arguments) for arguments in requests]
    print(
        json.dumps(
            {
                "scope": "instrumented bounded CLI calls, not performance acceptance",
                "requests": rows,
            }
        )
    )


if __name__ == "__main__":
    main()
