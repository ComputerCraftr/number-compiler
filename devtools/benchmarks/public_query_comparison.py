"""Compare current public CLI outputs and point demands without release thresholds."""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import subprocess
import sys
from collections.abc import Callable, Sequence
from time import perf_counter
from typing import Literal, TypedDict

from devtools.paths import report_output
from number_compiler.api.cli import main as cli_main
from number_compiler.api.cli_render import _radix_string
from number_compiler.api.cli_requests import CAPABILITIES
from number_compiler.api.number_api import NumberCompiler

Mode = Literal["cold", "warm", "bypass"]
FAMILIES = tuple(CAPABILITIES)


class Sample(TypedDict):
    family: str
    horizon: int
    trial: int
    mode: Mode
    phase: str
    route: str
    output_base: int
    seconds: float
    value: str
    info: object


def cli_sample(arguments: list[str], *, fresh: bool) -> tuple[float, dict[str, object]]:
    """Time only the requested CLI route; retain its actual metrics packet."""
    started = perf_counter()
    if fresh:
        process = subprocess.run(
            [sys.executable, "-m", "number_compiler", *arguments],
            capture_output=True,
            text=True,
            check=False,
        )
        code, output, error = process.returncode, process.stdout, process.stderr
    else:
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            code = cli_main(arguments)
        output, error = stdout.getvalue(), stderr.getvalue()
    elapsed = perf_counter() - started
    if code:
        raise ValueError(f"CLI refused comparison: exit {code}: {error or output}")
    packet = json.loads(output)
    if not isinstance(packet, dict) or not isinstance(packet.get("value"), str):
        raise TypeError("CLI did not emit an exact digit string")
    return elapsed, packet


def compare(
    family: str,
    horizons: Sequence[int],
    trials: int,
    modes: Sequence[Mode],
    *,
    seed: int = 27,
    bases: Sequence[int] = (2, 10),
    position: int = 2,
    max_output_bits: int = 1_000_000,
    on_sample: Callable[[Sample], None] | None = None,
) -> list[Sample]:
    """Retain every timed sample; check agreement outside each timed demand.

    The reference is a separate public API query, not an independent literal
    oracle. Comparisons establish route/output agreement, never temporal closure.
    Warm point queries reuse their compiler and execution owner. CLI warm queries
    reuse process caches; each CLI invocation still owns its own query context.
    """
    if family not in FAMILIES or trials < 1 or position < 0 or max_output_bits < 1:
        raise ValueError("invalid public comparison configuration")
    if not horizons or any(horizon < 0 for horizon in horizons):
        raise ValueError("horizons must be nonnegative")
    if not bases or any(base < 2 or base > 36 for base in bases):
        raise ValueError("output bases must be between 2 and 36")
    if not modes or any(mode not in ("cold", "warm", "bypass") for mode in modes):
        raise ValueError("invalid comparison mode")
    kwargs = {"seed": seed} if family in ("collatz", "reverse-add", "196") else {}
    rows: list[Sample] = []

    def record(sample: Sample) -> None:
        rows.append(sample)
        if on_sample is not None:
            on_sample(sample)

    for horizon in horizons:
        reference = NumberCompiler(max_cached_terms=0).nth(
            family, horizon, max_bits=max_output_bits, **kwargs
        )
        source_radix = 10 if family in ("196", "reverse-add", "a367620") else 2
        expected_digit = (reference // source_radix**position) % source_radix
        expected_outputs = {base: _radix_string(reference, base) for base in bases}
        for mode in modes:
            NumberCompiler.clear_shared_cache()
            compiler = NumberCompiler(
                max_cached_terms=0 if mode == "bypass" else 8,
                shared_cache=mode != "bypass",
            )
            samples = range(-1, trials) if mode == "warm" else range(trials)
            for trial in samples:
                phase = "priming" if trial == -1 else "measured"
                ordered_bases = tuple(reversed(bases)) if trial % 2 else tuple(bases)
                for base in ordered_bases:
                    if mode == "bypass":
                        NumberCompiler.clear_shared_cache()
                    arguments = [
                        family,
                        "--nth",
                        str(horizon),
                        "--output-base",
                        str(base),
                        "--max-output-bits",
                        str(max_output_bits),
                        "--format",
                        "json",
                        "--info",
                        "metrics",
                    ]
                    if kwargs:
                        arguments.extend(("--seed", str(seed)))
                    elapsed, packet = cli_sample(arguments, fresh=mode == "cold")
                    value = str(packet["value"])
                    record(
                        {
                            "family": family,
                            "horizon": horizon,
                            "trial": trial,
                            "mode": mode,
                            "phase": phase,
                            "route": "cli",
                            "output_base": base,
                            "seconds": elapsed,
                            "value": value,
                            "info": packet.get("info"),
                        }
                    )
                    if value != expected_outputs[base]:
                        raise AssertionError(
                            "public CLI output differs from API output"
                        )
                # A cold point demand has a fresh compiler and cleared process caches;
                # unlike cold CLI timing, its timing excludes interpreter startup.
                if mode in ("cold", "bypass"):
                    NumberCompiler.clear_shared_cache()
                    compiler = NumberCompiler(
                        max_cached_terms=0, shared_cache=mode != "bypass"
                    )
                started = perf_counter()
                term = compiler.project_nth(family, horizon, **kwargs)
                digit = term.digit(position)
                elapsed = perf_counter() - started
                record(
                    {
                        "family": family,
                        "horizon": horizon,
                        "trial": trial,
                        "mode": mode,
                        "phase": phase,
                        "route": "point",
                        "output_base": source_radix,
                        "seconds": elapsed,
                        "value": str(digit),
                        "info": {"position": position},
                    }
                )
                if digit != expected_digit:
                    raise AssertionError(
                        "public point demand differs from exact output"
                    )
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=FAMILIES, default="collatz")
    parser.add_argument("--horizons", type=int, nargs="+", default=[16, 32, 64])
    parser.add_argument("--trials", type=int, default=5)
    parser.add_argument(
        "--modes",
        choices=("cold", "warm", "bypass"),
        nargs="+",
        default=["cold", "warm", "bypass"],
    )
    parser.add_argument("--seed", type=int, default=27)
    parser.add_argument("--bases", type=int, nargs="+", default=[2, 10])
    parser.add_argument("--position", type=int, default=2)
    parser.add_argument("--max-output-bits", type=int, default=1_000_000)
    options = parser.parse_args()
    modes: list[Mode] = options.modes
    output = report_output(
        "devtools.benchmarks.public_query_comparison", "comparison.json"
    )
    payload: dict[str, object] = {
        "scope": "current public route/output agreement; API reference is not an independent oracle; no latency threshold or temporal complexity claim",
        "cold_cli_includes_interpreter_startup": True,
        "point_timings_include_project_nth": True,
        "warm_priming_samples_retained": True,
        "configuration": vars(options),
        "bypass_cli_policy": "clear process caches before each query; within-query memoization remains enabled",
        "bypass_point_shared_cache": False,
        "rows": [],
        "outcome": "running",
    }
    retained: list[Sample] = []

    def save_sample(sample: Sample) -> None:
        retained.append(sample)
        payload["rows"] = retained
        output.write_text(json.dumps(payload, indent=2) + "\n")

    output.write_text(json.dumps(payload, indent=2) + "\n")
    try:
        compare(
            options.family,
            options.horizons,
            options.trials,
            modes,
            seed=options.seed,
            bases=options.bases,
            position=options.position,
            max_output_bits=options.max_output_bits,
            on_sample=save_sample,
        )
    except BaseException:
        payload["outcome"] = "failed_or_interrupted"
        output.write_text(json.dumps(payload, indent=2) + "\n")
        raise
    payload["outcome"] = "completed"
    output.write_text(json.dumps(payload, indent=2) + "\n")
    print(output)
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
