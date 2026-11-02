"""Compare repeated installed CLI queries, preserving imports and query ownership."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
from contextlib import ExitStack
from pathlib import Path
from statistics import median
from typing import TypedDict, cast

from devtools.benchmarks.cli_startup import CASES, install_wheel


class PrimeSample(TypedDict):
    seconds: float
    value: object
    metrics: object


PROBE = """
import contextlib
import io
import json
import sys
from time import perf_counter
from number_compiler.api.cli import main
arguments = json.loads(sys.argv[1])
samples = int(sys.argv[2])
bypass = sys.argv[3] == 'bypass'
interactive = sys.argv[4:] == ['interactive']
rows = []
for repetition in range(samples + 1):
    if interactive and sys.stdin.readline().strip() != 'run':
        raise RuntimeError('missing paired benchmark request')
    stdout, stderr = io.StringIO(), io.StringIO()
    started = perf_counter()
    with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
        status = main(arguments, shared_cache=not bypass)
    elapsed = perf_counter() - started
    if status != 0 or stderr.getvalue():
        raise RuntimeError((status, stderr.getvalue()))
    packet = json.loads(stdout.getvalue())
    row = {'seconds': elapsed, 'value': packet['value'], 'metrics': packet['info']['metrics']}
    rows.append(row)
    if interactive:
        print(json.dumps(row), flush=True)
if not interactive:
    print(json.dumps(rows))
"""


def _prime_sample(value: object) -> PrimeSample:
    if type(value) is not dict:
        raise ValueError("prime benchmark response is not an object")
    packet = cast(dict[str, object], value)
    if set(packet) != {"seconds", "value", "metrics"}:
        raise ValueError("prime benchmark response has unexpected fields")
    seconds = packet["seconds"]
    if type(seconds) is int:
        seconds_value = float(seconds)
    elif type(seconds) is float:
        seconds_value = seconds
    else:
        raise ValueError("prime benchmark duration is not numeric")
    return {
        "seconds": seconds_value,
        "value": packet["value"],
        "metrics": packet["metrics"],
    }


def _prime_samples_json(text: str) -> list[PrimeSample]:
    value: object = json.loads(text)
    if type(value) is not list:
        raise ValueError("prime benchmark response is not an array")
    return [_prime_sample(item) for item in cast(list[object], value)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--samples", type=int, default=5)
    args = parser.parse_args()
    if not 1 <= args.samples <= 5:
        parser.error("samples must be 1..5")
    environment = dict(os.environ)
    environment.pop("PYTHONPATH", None)
    environment.pop("MYPYPATH", None)
    reports: dict[str, dict[str, list[PrimeSample]]] = {
        "baseline": {},
        "candidate": {},
    }
    with tempfile.TemporaryDirectory(prefix="number-compiler-prime-warm-") as temporary:
        work = Path(temporary)
        interpreters = {
            label: install_wheel(wheel.resolve(strict=True), work / label, environment)
            for label, wheel in (
                ("baseline", args.baseline),
                ("candidate", args.candidate),
            )
        }
        for name in ("prime", "prime-start"):
            arguments = [*CASES[name], "--info", "metrics"]
            with ExitStack() as stack:
                children: dict[str, subprocess.Popen[str]] = {}
                for label, python in interpreters.items():
                    children[label] = stack.enter_context(
                        subprocess.Popen(
                            [
                                str(python),
                                "-I",
                                "-c",
                                PROBE,
                                json.dumps(arguments),
                                str(args.samples),
                                "reuse",
                                "interactive",
                            ],
                            cwd=work,
                            env=environment,
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            text=True,
                        )
                    )
                    reports[label][name] = []
                for trial in range(args.samples + 1):
                    labels = tuple(children)
                    if trial % 2:
                        labels = tuple(reversed(labels))
                    for label in labels:
                        child = children[label]
                        assert child.stdin is not None and child.stdout is not None
                        child.stdin.write("run\n")
                        child.stdin.flush()
                        response = child.stdout.readline()
                        if not response:
                            raise RuntimeError(f"paired prime probe failed: {label}")
                        decoded: object = json.loads(response)
                        reports[label][name].append(_prime_sample(decoded))
                for child in children.values():
                    if child.wait(timeout=5):
                        raise RuntimeError("paired prime interpreter failed")
            run = subprocess.run(
                [
                    str(interpreters["candidate"]),
                    "-I",
                    "-c",
                    PROBE,
                    json.dumps(arguments),
                    str(args.samples),
                    "bypass",
                ],
                cwd=work,
                env=environment,
                check=True,
                capture_output=True,
                text=True,
            )
            reports["candidate"][name + "-bypass"] = _prime_samples_json(run.stdout)
    for name in ("prime", "prime-start"):
        values = [row["value"] for cases in reports.values() for row in cases[name]]
        if len(set(values)) != 1:
            raise AssertionError(f"warm CLI values differ: {name}")
    comparisons = {}
    for name in ("prime", "prime-start"):
        before = median(row["seconds"] for row in reports["baseline"][name][1:])
        after = median(row["seconds"] for row in reports["candidate"][name][1:])
        tolerance = max(0.1 * before, 0.001)
        comparisons[name] = {
            "baseline_median_seconds": before,
            "candidate_median_seconds": after,
            "tolerance_seconds": tolerance,
            "passes": after <= before + tolerance,
        }
        expected = reports["candidate"][name][0]["value"]
        if any(
            row["value"] != expected for row in reports["candidate"][name + "-bypass"]
        ):
            raise AssertionError("cache bypass changed the prime value")
    print(
        json.dumps(
            {
                "scope": "one cold and sampled warm CLI calls per installed interpreter; candidate also bypasses shared cache",
                "trial_order": "paired baseline/candidate requests, alternating first interpreter",
                "warm_samples": args.samples,
                "semantic_match": True,
                "comparisons": comparisons,
                "reports": reports,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
