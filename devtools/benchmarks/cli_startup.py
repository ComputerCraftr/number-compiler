"""Compare fresh CLI processes from two isolated installed wheels."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import tempfile
from time import perf_counter
from typing import Any


CASES = {
    "families": ["--list-families"],
    "prime": ["prime", "--nth", "1000", "--format", "json"],
    "prime-start": ["prime", "--nth", "0", "--start", "10000", "--format", "json"],
    "196": ["196", "--nth", "8", "--format", "json"],
    "collatz": ["collatz", "--nth", "64", "--seed", "27", "--format", "json"],
    "antihydra": ["antihydra", "--nth", "512", "--info", "ledger", "--info", "clock",
                  "--format", "json"],
    "fermat": ["fermat", "--nth", "0", "--no-value", "--info", "primality", "--format", "json"],
    "mersenne": ["mersenne", "--nth", "11", "--no-value", "--info", "factor", "--format", "json"],
}


def _install(wheel: Path, directory: Path, environment: dict[str, str]) -> Path:
    subprocess.run([sys.executable, "-m", "venv", str(directory)], check=True,
                   env=environment, capture_output=True, timeout=15)
    python = directory / ("Scripts/python.exe" if os.name == "nt" else "bin/python")
    subprocess.run([str(python), "-m", "pip", "install", "--no-deps", "--no-index", str(wheel)],
                   check=True, env=environment, capture_output=True, timeout=15)
    return python


def _semantic(stdout: str, name: str) -> Any:
    if name == "families":
        return stdout
    packet = json.loads(stdout)
    information = {
        kind: value.get("value", {key: value.get(key) for key in
                                 ("status", "factor_witness", "factor_expression")})
        for kind, value in packet["info"].items()
    }
    return {key: value for key, value in packet.items() if key != "info"}, information


def compare(baseline: Path, candidate: Path, *, samples: int = 3,
            cases: list[str] | None = None) -> dict[str, Any]:
    if not 1 <= samples <= 5:
        raise ValueError("samples must be 1..5")
    environment = dict(os.environ)
    environment.pop("PYTHONPATH", None)
    environment.pop("MYPYPATH", None)
    rows: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="number-compiler-cli-timing-") as temporary:
        work = Path(temporary)
        interpreters = {
            "baseline": _install(baseline.resolve(strict=True), work / "baseline", environment),
            "candidate": _install(candidate.resolve(strict=True), work / "candidate", environment),
        }
        for name in dict.fromkeys(CASES if cases is None else cases):
            arguments = CASES[name]
            values: list[Any] = []
            measurements: dict[str, list[float]] = {label: [] for label in interpreters}
            for trial in range(samples):
                # Pair each baseline/candidate trial and alternate ordering to
                # avoid assigning all filesystem/host drift to the candidate.
                labels = tuple(interpreters)
                if trial % 2:
                    labels = tuple(reversed(labels))
                for label in labels:
                    python = interpreters[label]
                    started = perf_counter()
                    completed = subprocess.run(
                        [str(python), "-I", "-m", "number_compiler", *arguments],
                        cwd=work, env=environment, capture_output=True, text=True,
                        check=True, timeout=5,
                    )
                    measurements[label].append(perf_counter() - started)
                    if completed.stderr:
                        raise AssertionError(completed.stderr)
                    values.append(_semantic(completed.stdout, name))
            if any(value != values[0] for value in values):
                raise AssertionError(f"installed semantic mismatch: {name}")
            before = statistics.median(measurements["baseline"])
            after = statistics.median(measurements["candidate"])
            rows.append({"case": name, "arguments": arguments, "seconds": measurements,
                         "baseline_median_seconds": before, "candidate_median_seconds": after,
                         "speedup": before / after, "semantic_match": True})
    return {
        "scope": "fresh processes with normal filesystem caches; imports and requested execution included",
        "trial_order": "paired baseline/candidate, alternating first interpreter",
        "baseline_sha256": hashlib.sha256(baseline.read_bytes()).hexdigest(),
        "candidate_sha256": hashlib.sha256(candidate.read_bytes()).hexdigest(),
        "samples_per_case_and_wheel": samples, "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--case", choices=tuple(CASES), action="append", dest="cases",
                        help="select cases to keep each batch within the process guard")
    args = parser.parse_args()
    print(json.dumps(compare(args.baseline, args.candidate, samples=args.samples,
                             cases=args.cases), indent=2))


if __name__ == "__main__":
    main()
