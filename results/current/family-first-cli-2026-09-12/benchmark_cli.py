"""Measure actual cold CLI startup and repeated in-process family queries."""

from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
from time import perf_counter


def main() -> None:
    arguments = [
        "antihydra",
        "--nth",
        "512",
        "--info",
        "ledger",
        "--info",
        "clock",
        "--info",
        "metrics",
        "--format",
        "json",
    ]
    started = perf_counter()
    cold = subprocess.run(
        [sys.executable, "-m", "number_compiler", *arguments],
        capture_output=True,
        text=True,
        check=True,
    )
    cold_seconds = perf_counter() - started
    expected = json.loads(cold.stdout)
    assert cold.stderr == ""

    from number_compiler.api.cli import main as cli_main
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.cli_requests import parse_request
    from number_compiler.api.number_api import AntihydraTermPayload, NumberCompiler

    warm_seconds = []
    for _ in range(3):
        out, err = io.StringIO(), io.StringIO()
        started = perf_counter()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = cli_main(arguments)
        warm_seconds.append(perf_counter() - started)
        assert status == 0 and not err.getvalue()
        assert json.loads(out.getvalue()) == expected

    request = parse_request(arguments + ["--no-value"])
    assert request is not None
    context = QueryContext(request, NumberCompiler())
    context.information()
    payload = context.term.payload
    assert isinstance(payload, AntihydraTermPayload)
    before = dict(payload.term.ledger.counters)
    context.information()
    after = dict(payload.term.ledger.counters)
    assert before == after
    print(
        json.dumps(
            {
                "arguments": arguments,
                "cold_cli_seconds": cold_seconds,
                "warm_process_fresh_query_seconds": warm_seconds,
                "warm_process_scope": "imports warm; each CLI call constructs a fresh query owner",
                "repeated_same_query_additional_work": {},
                "metrics": expected["info"]["metrics"],
                "same_query_counters": after,
                "scope": "512 finite returns; source discovery is charged, not assumed cheap",
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
