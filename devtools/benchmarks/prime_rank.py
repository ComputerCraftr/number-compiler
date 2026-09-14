"""Compare repeated installed CLI queries, preserving imports and query ownership."""

from __future__ import annotations

import argparse
from contextlib import ExitStack
import json
import os
from statistics import median
from pathlib import Path
import subprocess
import tempfile
from typing import TypedDict

from devtools.benchmarks.cli_startup import CASES, _install


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
if bypass:
    import number_compiler.api.cli as cli
    from number_compiler.api.number_api import NumberCompiler
    def isolated_compiler():
        return NumberCompiler(shared_cache=False)
    cli.NumberCompiler = isolated_compiler
rows = []
for repetition in range(samples + 1):
    if interactive and sys.stdin.readline().strip() != 'run':
        raise RuntimeError('missing paired benchmark request')
    stdout, stderr = io.StringIO(), io.StringIO()
    started = perf_counter()
    with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
        status = main(arguments)
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
        'baseline': {}, 'candidate': {},
    }
    with tempfile.TemporaryDirectory(prefix="number-compiler-prime-warm-") as temporary:
        work = Path(temporary)
        interpreters = {
            label: _install(wheel.resolve(strict=True), work / label, environment)
            for label, wheel in (("baseline", args.baseline), ("candidate", args.candidate))
        }
        for name in ("prime", "prime-start"):
            arguments = [*CASES[name], "--info", "metrics"]
            with ExitStack() as stack:
                children = {}
                for label, python in interpreters.items():
                    children[label] = stack.enter_context(subprocess.Popen(
                        [str(python), "-I", "-c", PROBE, json.dumps(arguments),
                         str(args.samples), "reuse", "interactive"],
                        cwd=work, env=environment, stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                    ))
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
                        reports[label][name].append(json.loads(response))
                for child in children.values():
                    if child.wait(timeout=5):
                        raise RuntimeError("paired prime interpreter failed")
            run = subprocess.run(
                [str(interpreters['candidate']), "-I", "-c", PROBE, json.dumps(arguments),
                 str(args.samples), "bypass"],
                cwd=work, env=environment, check=True, capture_output=True,
                text=True, timeout=5,
            )
            reports['candidate'][name + '-bypass'] = json.loads(run.stdout)
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
            "baseline_median_seconds": before, "candidate_median_seconds": after,
            "tolerance_seconds": tolerance, "passes": after <= before + tolerance,
        }
        expected = reports["candidate"][name][0]["value"]
        if any(row["value"] != expected for row in reports["candidate"][name + "-bypass"]):
            raise AssertionError("cache bypass changed the prime value")
    print(json.dumps({
        "scope": "one cold and sampled warm CLI calls per installed interpreter; candidate also bypasses shared cache",
        "trial_order": "paired baseline/candidate requests, alternating first interpreter",
        "warm_samples": args.samples,
        "semantic_match": True, "comparisons": comparisons, "reports": reports,
    }, indent=2))


if __name__ == "__main__":
    main()
