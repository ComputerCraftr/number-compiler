"""Compare the fixed-seed Antihydra odd macro with its exact fallback route.

The public family is pinned to source 8, so this benchmark intentionally has
no seed argument. It uses the production CLI for both total arithmetic and the
information-only Mahler consumer, disables only the odd-macro candidate owner
for the comparison route, and reads actual work from schema-eight metrics.
"""

from __future__ import annotations

import argparse
import statistics
from collections.abc import Callable, Iterator, Sequence
from contextlib import contextmanager, nullcontext
from importlib import import_module
from typing import Literal, TypedDict
from unittest.mock import patch

from devtools.benchmarks.public_query_comparison import (
    cli_sample,
    family_execution_work,
    named_counter_lane,
    run_jsonl_report,
)
from number_compiler.api.family_registry import option_argv
from number_compiler.api.number_api import NumberCompiler

Consumer = Literal["antihydra", "mahler"]
Mode = Literal["enabled", "odd_macro_disabled"]
DEFAULT_HORIZONS = (65, 128, 1024)
DEFAULT_CONSUMERS: tuple[Consumer, ...] = ("antihydra", "mahler")


class Sample(TypedDict):
    consumer: Consumer
    horizon: int
    trial: int
    mode: Mode
    seconds: float
    value: str | None
    odd_macro_work: dict[str, int] | None
    info: object


def _arguments(consumer: Consumer, horizon: int) -> list[str]:
    arguments = [
        "antihydra",
        *option_argv("nth", horizon),
        *option_argv("info", "metrics"),
        *option_argv("format", "json"),
    ]
    if consumer == "mahler":
        arguments.extend(
            [
                *option_argv("no_value", True),
                *option_argv("info", "arithmetic.mahler"),
            ]
        )
    return arguments


def _no_odd_macro(*_args: object, **_kwargs: object) -> None:
    return None


@contextmanager
def _odd_macro_disabled() -> Iterator[None]:
    """Keep the scheduler and exact fallback, disabling only the macro owner."""
    module = import_module("number_compiler.sequences.antihydra.arithmetic_images")
    workspace_type = module.AntihydraArithmeticImageWorkspace
    with patch.object(
        workspace_type,
        "_try_odd_macro_candidate",
        new=_no_odd_macro,
    ):
        yield


def _odd_work(packet: dict[str, object]) -> dict[str, int] | None:
    _info, _metrics, _execution, row = family_execution_work(
        packet, "antihydra_arithmetic"
    )
    counters = named_counter_lane(row.get("odd_macro_work"), "odd_macro_work")
    return counters


def _sample(
    consumer: Consumer,
    horizon: int,
    trial: int,
    mode: Mode,
) -> Sample:
    NumberCompiler.clear_shared_cache()
    arguments = _arguments(consumer, horizon)
    route = _odd_macro_disabled() if mode == "odd_macro_disabled" else nullcontext()
    try:
        with route:
            elapsed, packet = cli_sample(arguments, fresh=False)
    finally:
        NumberCompiler.clear_shared_cache()
    info = packet.get("info")
    if not isinstance(info, dict):
        raise TypeError("Antihydra CLI omitted the information object")
    expected_info = (
        {"metrics"} if consumer == "antihydra" else {"arithmetic.mahler", "metrics"}
    )
    if set(info) != expected_info:
        raise AssertionError("Antihydra CLI returned the wrong observation keys")
    value = packet.get("value")
    if consumer == "mahler":
        if value is not None:
            raise AssertionError("Mahler information-only query rendered a value")
    elif not isinstance(value, str):
        raise TypeError("Antihydra CLI omitted its requested arithmetic value")
    odd = _odd_work(packet)
    return Sample(
        consumer=consumer,
        horizon=horizon,
        trial=trial,
        mode=mode,
        seconds=elapsed,
        value=value if isinstance(value, str) else None,
        odd_macro_work=odd,
        info={key: value for key, value in info.items() if key != "metrics"},
    )


def compare(
    horizons: Sequence[int] = DEFAULT_HORIZONS,
    consumers: Sequence[Consumer] = DEFAULT_CONSUMERS,
    trials: int = 5,
    *,
    on_sample: Callable[[Sample], None] | None = None,
) -> dict[str, object]:
    if type(trials) is not int or trials < 1:
        raise ValueError("trial count must be positive")
    if not horizons or any(
        type(horizon) is not int or horizon < 0 for horizon in horizons
    ):
        raise ValueError("horizons must be nonnegative integers")
    if not consumers or any(value not in DEFAULT_CONSUMERS for value in consumers):
        raise ValueError("unsupported Antihydra odd-macro consumer")
    samples: list[Sample] = []
    stable_packets: dict[tuple[Consumer, int], tuple[str | None, object]] = {}
    for consumer in consumers:
        for horizon in horizons:
            for mode in ("enabled", "odd_macro_disabled"):
                _sample(consumer, horizon, -1, mode)
    for consumer in consumers:
        for horizon in horizons:
            for trial in range(trials):
                modes: tuple[Mode, Mode] = (
                    ("enabled", "odd_macro_disabled")
                    if trial % 2 == 0
                    else ("odd_macro_disabled", "enabled")
                )
                for mode in modes:
                    sample = _sample(consumer, horizon, trial, mode)
                    samples.append(sample)
                    if on_sample is not None:
                        on_sample(sample)
                    key = consumer, horizon
                    stable_packet = (sample["value"], sample["info"])
                    previous = stable_packets.get(key)
                    if previous is None:
                        stable_packets[key] = stable_packet
                    elif stable_packet != previous:
                        raise AssertionError(
                            "Antihydra/Mahler value or observation changed across routes"
                        )
            enabled = [
                row
                for row in samples
                if row["consumer"] == consumer
                and row["horizon"] == horizon
                and row["mode"] == "enabled"
            ]
            disabled = [
                row
                for row in samples
                if row["consumer"] == consumer
                and row["horizon"] == horizon
                and row["mode"] == "odd_macro_disabled"
            ]
            if any(
                (row["odd_macro_work"] or {}).get("evaluations", 0) > 0
                for row in disabled
            ):
                raise AssertionError("odd-macro-disabled route still evaluated a macro")
            if consumer == "antihydra" and any(
                row["value"] != enabled[0]["value"] for row in disabled
            ):
                raise AssertionError("Antihydra endpoint changed under macro ablation")
    summaries = []
    for consumer in consumers:
        for horizon in horizons:
            enabled = [
                row
                for row in samples
                if row["consumer"] == consumer
                and row["horizon"] == horizon
                and row["mode"] == "enabled"
            ]
            disabled = [
                row
                for row in samples
                if row["consumer"] == consumer
                and row["horizon"] == horizon
                and row["mode"] == "odd_macro_disabled"
            ]
            enabled_times = [row["seconds"] for row in enabled]
            disabled_times = [row["seconds"] for row in disabled]
            enabled_work = [row["odd_macro_work"] for row in enabled]
            disabled_work = [row["odd_macro_work"] for row in disabled]
            evaluations = [
                None if work is None else work.get("evaluations", 0)
                for work in enabled_work
            ]
            summaries.append(
                {
                    "consumer": consumer,
                    "horizon": horizon,
                    "seed": 8,
                    "seed_authority": "fixed Antihydra CLI source; no seed option",
                    "info_only": consumer == "mahler",
                    "enabled_median_seconds": statistics.median(enabled_times),
                    "odd_macro_disabled_median_seconds": statistics.median(
                        disabled_times
                    ),
                    "disabled_over_enabled_time_ratio": (
                        statistics.median(disabled_times)
                        / statistics.median(enabled_times)
                        if statistics.median(enabled_times)
                        else None
                    ),
                    "enabled_macro_hit": any(
                        count is not None and count > 0 for count in evaluations
                    ),
                    "enabled_macro_evaluations": evaluations,
                    "disabled_macro_evaluations": [
                        None if work is None else work.get("evaluations", 0)
                        for work in disabled_work
                    ],
                    "enabled_odd_macro_work": enabled_work,
                    "disabled_odd_macro_work": disabled_work,
                }
            )
    return {
        "scope": (
            "same fixed source and same CLI request per consumer/horizon; "
            "enabled route compared with only _try_odd_macro_candidate disabled; "
            "one unrecorded warm-up request per route; query caches cleared before "
            "every request; timed samples include requested output"
        ),
        "seed": 8,
        "seed_authority": "fixed Antihydra CLI source; no arbitrary seed option",
        "horizons": tuple(horizons),
        "trials": trials,
        "consumers": tuple(consumers),
        "unrecorded_warmup_queries_per_route": 1,
        "macro_hit_policy": "null or zero evaluations are reported as no hit; not a failure",
        "summaries": summaries,
        "samples": samples,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--horizons", type=int, nargs="+", default=list(DEFAULT_HORIZONS)
    )
    parser.add_argument(
        "--consumers",
        choices=DEFAULT_CONSUMERS,
        nargs="+",
        default=list(DEFAULT_CONSUMERS),
    )
    parser.add_argument("--trials", type=int, default=5)
    options = parser.parse_args()
    configuration: dict[str, object] = {
        "horizons": options.horizons,
        "consumers": options.consumers,
        "trials": options.trials,
        "seed": 8,
    }

    def run(on_sample: Callable[[Sample], None]) -> dict[str, object]:
        return compare(
            options.horizons,
            options.consumers,
            options.trials,
            on_sample=on_sample,
        )

    return run_jsonl_report(
        "devtools.benchmarks.antihydra_odd_macro_ablation",
        "comparison.json",
        "same-source public CLI; exact source pinned to Antihydra seed 8",
        configuration,
        run,
        run_metadata={
            "seed": 8,
            "seed_authority": "fixed Antihydra CLI source; no seed option",
            "unrecorded_warmup_queries_per_route": 1,
        },
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
