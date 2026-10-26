"""Compare public CLI values or named observations across cache modes."""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import subprocess
import sys
from collections.abc import Callable, Sequence
from time import perf_counter
from typing import Literal, TypedDict, TypeVar

from devtools.paths import report_output
from number_compiler.api.cli import main as cli_main
from number_compiler.api.cli_render import radix_string
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.family_registry import CAPABILITIES, family_spec
from number_compiler.api.json_output import (
    is_object_sequence,
    is_string_object_mapping,
)
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.query_types import AntihydraVerifyQuery, CollatzEventQuery
from number_compiler.api.registry_cli import option_argv
from number_compiler.arithmetic.contracts.family_identity import family_id

Mode = Literal["cold", "warm", "bypass"]
FAMILIES = tuple(CAPABILITIES)
_SampleT = TypeVar("_SampleT")


class Sample(TypedDict):
    family: str
    horizon: int
    trial: int
    mode: Mode
    phase: str
    route: str
    output_base: int
    seconds: float
    value: str | None
    info: object


def cli_invocation(
    arguments: list[str], *, fresh: bool, shared_cache: bool = True
) -> tuple[float, int, str, str]:
    """Run one CLI request and return elapsed time plus its raw process result."""
    started = perf_counter()
    if fresh:
        if not shared_cache:
            raise ValueError(
                "cache-bypassed CLI measurement requires embedded execution"
            )
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
            code = cli_main(arguments, shared_cache=shared_cache)
        output, error = stdout.getvalue(), stderr.getvalue()
    elapsed = perf_counter() - started
    return elapsed, code, output, error


def cli_sample(
    arguments: list[str], *, fresh: bool, shared_cache: bool = True
) -> tuple[float, dict[str, object]]:
    """Time a successful CLI route and retain its actual metrics packet."""
    elapsed, code, output, error = cli_invocation(
        arguments, fresh=fresh, shared_cache=shared_cache
    )
    if code:
        raise ValueError(f"CLI refused comparison: exit {code}: {error or output}")
    decoded: object = json.loads(output)
    if not is_string_object_mapping(decoded):
        raise TypeError("CLI did not emit a JSON query packet")
    packet: dict[str, object] = dict(decoded)
    value = packet.get("value")
    if value is not None and not isinstance(value, str):
        raise TypeError("CLI value must be an exact digit string or null")
    return elapsed, packet


def named_counter_lane(value: object, label: str) -> dict[str, int] | None:
    """Parse a nullable schema-eight named-work lane without inventing zeros."""
    if value is None:
        return None
    if not is_object_sequence(value) or type(value) is not list:
        raise TypeError(f"{label} must be a JSON list of counter pairs")
    counts: dict[str, int] = {}
    for pair in value:
        if (
            not is_object_sequence(pair)
            or type(pair) is not list
            or len(pair) != 2
            or not isinstance(pair[0], str)
            or type(pair[1]) is not int
            or pair[1] < 0
        ):
            raise TypeError(f"{label} contains an invalid counter pair")
        if pair[0] in counts:
            raise TypeError(f"{label} repeats a counter name")
        counts[pair[0]] = pair[1]
    return counts


def family_execution_work(
    packet: dict[str, object], counter_prefix: str
) -> tuple[dict[str, object], dict[str, object], dict[str, object], dict[str, object]]:
    """Select one instrumented family row from a public CLI metrics packet."""
    info = packet.get("info")
    if not is_string_object_mapping(info) or "metrics" not in info:
        raise TypeError("CLI did not return its requested metrics packet")
    info_packet: dict[str, object] = dict(info)
    metrics = info_packet["metrics"]
    if not is_string_object_mapping(metrics):
        raise TypeError("metrics observation is not an object")
    metrics_packet: dict[str, object] = dict(metrics)
    execution = metrics_packet.get("execution_metrics")
    if not is_string_object_mapping(execution):
        raise TypeError("metrics omitted execution-work measurements")
    execution_packet: dict[str, object] = dict(execution)
    rows = execution_packet.get("family_work")
    if not is_object_sequence(rows):
        raise TypeError("execution metrics omitted family work rows")
    matches: list[dict[str, object]] = []
    for row in rows:
        if (
            is_string_object_mapping(row)
            and row.get("counter_prefix") == counter_prefix
        ):
            matches.append(dict(row))
    if len(matches) != 1:
        raise TypeError(f"execution metrics need one {counter_prefix} family work row")
    return info_packet, metrics_packet, execution_packet, matches[0]


def run_jsonl_report(
    module: str,
    report_name: str,
    scope: str,
    configuration: dict[str, object],
    run: Callable[[Callable[[_SampleT], None]], dict[str, object]],
    *,
    run_metadata: dict[str, object] | None = None,
) -> int:
    """Run and journal a bounded benchmark, preserving partial samples on error."""
    output = report_output(module, report_name)
    journal_path = output.with_name("samples.jsonl")
    payload: dict[str, object] = {
        "scope": scope,
        "configuration": configuration,
        "sample_journal": journal_path.name,
        "rows": [],
        "outcome": "running",
    }
    if run_metadata is not None:
        payload.update(run_metadata)
    retained: list[_SampleT] = []
    payload["rows"] = retained
    output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    try:
        with journal_path.open("x", encoding="utf-8") as journal:

            def save_sample(sample: _SampleT) -> None:
                retained.append(sample)
                journal.write(json.dumps(sample) + "\n")
                journal.flush()

            result = run(save_sample)
    except BaseException as error:
        payload["outcome"] = "failed_or_interrupted"
        payload["error"] = {"type": type(error).__name__, "detail": str(error)}
        output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        raise
    payload.update(result)
    payload["outcome"] = "completed"
    output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(output)
    return 0


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
    info: Sequence[str] = ("metrics",),
    no_value: bool = False,
    on_sample: Callable[[Sample], None] | None = None,
) -> list[Sample]:
    """Retain every timed sample; check agreement outside each timed demand.

    The reference is a separate public API query, not an independent literal
    oracle. Comparisons establish route/output agreement, never temporal closure.
    Warm point queries reuse their compiler and execution owner. CLI warm queries
    reuse process caches; each CLI invocation still owns its own query context.
    """
    selected_family = family_id(family)
    if (
        selected_family not in FAMILIES
        or trials < 1
        or position < 0
        or max_output_bits < 1
    ):
        raise ValueError("invalid public comparison configuration")
    if type(no_value) is not bool:
        raise ValueError("no_value must be Boolean")
    if not info or any(type(name) is not str for name in info):
        raise ValueError("at least one named CLI observation is required")
    spec = family_spec(selected_family)
    supported_info = set(spec.nth_info)
    if any(name not in supported_info for name in info):
        raise ValueError("CLI observation is not supported by the selected family")
    if not horizons or any(horizon < 0 for horizon in horizons):
        raise ValueError("horizons must be nonnegative")
    if not bases or any(base < 2 or base > 36 for base in bases):
        raise ValueError("output bases must be between 2 and 36")
    if not modes or any(mode not in ("cold", "warm", "bypass") for mode in modes):
        raise ValueError("invalid comparison mode")
    source_arguments = option_argv("seed", seed) if "seed" in spec.parameters else []
    requested_info = tuple(dict.fromkeys(info))
    selected_bases = tuple(bases[:1]) if no_value else tuple(bases)
    rows: list[Sample] = []

    def record(sample: Sample) -> None:
        rows.append(sample)
        if on_sample is not None:
            on_sample(sample)

    for horizon in horizons:
        source_request = parse_request(
            [family, *option_argv("nth", horizon), *source_arguments]
        )
        assert source_request is not None
        query = source_request.execution
        assert not isinstance(query, (AntihydraVerifyQuery, CollatzEventQuery))
        if no_value:
            expected_digit: int | None = None
            expected_outputs: dict[int, str] = {}
            source_radix = 2
        else:
            projected = NumberCompiler(max_cached_terms=0).project(query)
            reference = projected.materialize(max_bits=max_output_bits)
            source_radix = projected.source_radix or 2
            expected_digit = (reference // source_radix**position) % source_radix
            expected_outputs = {
                base: radix_string(reference, base) for base in selected_bases
            }
        semantic_info: object | None = None
        for mode in modes:
            NumberCompiler.clear_shared_cache()
            compiler = NumberCompiler(
                max_cached_terms=0 if mode == "bypass" else 8,
                shared_cache=mode != "bypass",
            )
            samples = range(-1, trials) if mode == "warm" else range(trials)
            for trial in samples:
                phase = "priming" if trial == -1 else "measured"
                ordered_bases = (
                    tuple(reversed(selected_bases)) if trial % 2 else selected_bases
                )
                for base in ordered_bases:
                    if mode == "bypass":
                        NumberCompiler.clear_shared_cache()
                    arguments = [
                        family,
                        *option_argv("nth", horizon),
                        *option_argv("output_base", base),
                        *option_argv("max_output_bits", max_output_bits),
                        *option_argv("format", "json"),
                        *[
                            argument
                            for name in requested_info
                            for argument in option_argv("info", name)
                        ],
                        *source_arguments,
                    ]
                    if no_value:
                        arguments.extend(option_argv("no_value", True))
                    elapsed, packet = cli_sample(
                        arguments, fresh=mode == "cold", shared_cache=mode != "bypass"
                    )
                    raw_value = packet.get("value")
                    value = raw_value if isinstance(raw_value, str) else None
                    raw_info = packet.get("info")
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
                            "info": raw_info,
                        }
                    )
                    if no_value and raw_value is not None:
                        raise AssertionError(
                            "CLI rendered a value for an info-only query"
                        )
                    if not no_value and value is None:
                        raise AssertionError("CLI omitted the requested exact value")
                    if not no_value and value != expected_outputs[base]:
                        raise AssertionError(
                            "public CLI output differs from API output"
                        )
                    if not is_string_object_mapping(raw_info):
                        raise TypeError("CLI did not return requested information")
                    if set(raw_info) != set(requested_info):
                        raise AssertionError("CLI returned the wrong information keys")
                    stable_info: dict[str, object] = {
                        key: item for key, item in raw_info.items() if key != "metrics"
                    }
                    if stable_info:
                        if semantic_info is None:
                            semantic_info = stable_info
                        elif stable_info != semantic_info:
                            raise AssertionError(
                                "CLI observation changed across cache modes or trials"
                            )
                # A cold point demand has a fresh compiler and cleared process caches;
                # unlike cold CLI timing, its timing excludes interpreter startup.
                if no_value:
                    continue
                if mode in ("cold", "bypass"):
                    NumberCompiler.clear_shared_cache()
                    compiler = NumberCompiler(
                        max_cached_terms=0, shared_cache=mode != "bypass"
                    )
                started = perf_counter()
                term = compiler.project(query)
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
    parser.add_argument(
        "--info",
        action="append",
        dest="information",
        help="repeatable CLI observation; defaults to metrics",
    )
    parser.add_argument(
        "--no-value",
        action="store_true",
        help="time information-only CLI requests without output rendering",
    )
    options = parser.parse_args()
    modes: list[Mode] = options.modes
    information = tuple(options.information or ("metrics",))
    selected_family = family_id(options.family)
    selected_spec = family_spec(selected_family)
    unsupported = set(information) - set(selected_spec.nth_info)
    if unsupported:
        parser.error(
            f"unsupported observation for {options.family}: "
            + ", ".join(sorted(unsupported))
        )
    if options.no_value:
        options.bases = options.bases[:1]
    configuration = vars(options).copy()
    configuration["seed"] = options.seed if "seed" in selected_spec.parameters else None
    output = report_output(
        "devtools.benchmarks.public_query_comparison", "comparison.json"
    )
    payload: dict[str, object] = {
        "scope": "current public route/output agreement; API reference is not an independent oracle; no latency threshold or temporal complexity claim",
        "cold_cli_includes_interpreter_startup": True,
        "point_timings_include_project": True,
        "warm_priming_samples_retained": True,
        "configuration": configuration,
        "bypass_cli_policy": "disable process-cache retrieval and publication; within-query memoization remains enabled",
        "bypass_point_shared_cache": False,
        "information": tuple(dict.fromkeys(information)),
        "no_value": options.no_value,
        "observation_comparison": "all non-metrics information packets must be structurally equal across cold, warm, and bypass modes",
        "rows": [],
        "outcome": "running",
        "sample_journal": "samples.jsonl",
    }
    retained: list[Sample] = []
    payload["rows"] = retained
    output.write_text(json.dumps(payload, indent=2) + "\n")
    try:
        # Keep crash evidence without repeatedly serializing all preceding
        # samples. The watchdog can kill the process before final reporting;
        # each completed sample is independently recoverable from this journal.
        with output.with_name("samples.jsonl").open("x", encoding="utf-8") as journal:

            def save_sample(sample: Sample) -> None:
                retained.append(sample)
                journal.write(json.dumps(sample) + "\n")
                journal.flush()

            compare(
                options.family,
                options.horizons,
                options.trials,
                modes,
                seed=options.seed,
                bases=options.bases,
                position=options.position,
                max_output_bits=options.max_output_bits,
                info=information,
                no_value=options.no_value,
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
