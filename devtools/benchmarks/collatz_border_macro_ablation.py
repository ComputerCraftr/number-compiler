"""Measure named and mixed Collatz macro routes against exact fallback.

The constructed source is admitted by the 6305 ring's exact 2-adic cylinder.
All modes run the same public CLI query and literal physical reference. The
first ablation disables only the named border-return selector. The second also
disables the mixed-clock macro selector, retaining the ordinary exact fallback.
Consumed work is read from execution metrics; timings are evidence, not a
release threshold.
"""

from __future__ import annotations

import argparse
import statistics
from collections.abc import Callable, Generator
from contextlib import ExitStack, contextmanager, nullcontext
from importlib import import_module
from typing import Literal, TypedDict
from unittest.mock import patch

from devtools.benchmarks.public_query_comparison import (
    cli_sample,
    family_execution_work,
    named_counter_lane,
    run_jsonl_report,
)
from devtools.benchmarks.report_schema import record
from devtools.verification.oracles.sequence_arithmetic import collatz_literal
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.registry_cli import option_argv
from number_compiler.sequences.collatz.border_harmonic_ring import (
    PeriodicTail6305Ring,
)

Mode = Literal["enabled", "selector_disabled", "all_selectors_disabled"]


class Sample(TypedDict):
    mode: Mode
    trial: int
    seconds: float
    value: str
    border_actions: int
    border_macro_physical_ticks: int | None
    conditional_physical_ticks: int | None
    mixed_macro_actions: int | None
    mixed_macro_repetitions: int | None
    mixed_macro_physical_ticks: int | None
    macro: object
    execution_metrics: object


class MacroSummary(TypedDict):
    macro: dict[str, object]
    border_actions: int
    border_macro_physical_ticks: int | None
    conditional_physical_ticks: int | None
    mixed_macro_actions: int | None
    mixed_macro_repetitions: int | None
    mixed_macro_physical_ticks: int | None


def source_for(motif: tuple[int, ...], groups: int) -> int:
    residue, modulus = PeriodicTail6305Ring.guard_residue(motif, groups)
    source = residue + modulus * ((3 - residue) * pow(modulus, -1, 5) % 5)
    return source


def _run_arguments(source: int, ticks: int) -> list[str]:
    return [
        "collatz",
        *option_argv("seed", source),
        *option_argv("nth", ticks),
        *option_argv("info", "temporal.macro"),
        *option_argv("info", "metrics"),
        *option_argv("format", "json"),
    ]


def _disabled_selector(*_args: object, **_kwargs: object) -> None:
    return None


@contextmanager
def selector_ablation(*, include_mixed: bool = False) -> Generator[None, None, None]:
    """Disable named 6305 selector call sites and optionally mixed selection."""
    execution = import_module(
        "number_compiler.sequences.collatz.temporal_border_return_execution"
    )
    unified = import_module("number_compiler.sequences.collatz.unified_skew_admission")
    with ExitStack() as stack:
        stack.enter_context(
            patch.object(execution, "select_border_return_macro", _disabled_selector)
        )
        stack.enter_context(
            patch.object(unified, "select_border_return_macro", _disabled_selector)
        )
        if include_mixed:
            conditional = import_module(
                "number_compiler.sequences.collatz.conditional_scheduler_adapter"
            )
            stack.enter_context(
                patch.object(
                    conditional,
                    "issue_conditional_scheduler_candidate",
                    _disabled_selector,
                )
            )
            mixed = import_module(
                "number_compiler.sequences.collatz.temporal_mixed_execution"
            )
            stack.enter_context(
                patch.object(mixed, "select_mixed_clock_macro", _disabled_selector)
            )
        yield


def packets(packet: dict[str, object]) -> tuple[MacroSummary, object]:
    info, _metrics, execution, collatz_work = family_execution_work(
        packet, "collatz_physical"
    )
    if set(info) != {"temporal.macro", "metrics"}:
        raise TypeError("CLI did not return the requested Collatz observations")
    macro = record(info["temporal.macro"])
    actions = macro.get("executed_macro_actions")
    actions = record(actions)
    action_count = actions.get("6305R")
    if type(action_count) is not int or action_count < 0:
        raise TypeError("temporal.macro omitted the measured 6305R count")
    mixed = named_counter_lane(collatz_work.get("mixed_clock_work"), "mixed_clock_work")
    conditional = named_counter_lane(
        collatz_work.get("conditional_scheduler_work"), "conditional_scheduler_work"
    )
    border = named_counter_lane(
        collatz_work.get("border_return_work"), "border_return_work"
    )
    if action_count and (
        border is None
        or "3_reentries" not in border
        or "zero_tail_symbols" not in border
    ):
        raise TypeError("6305R action count lacks its applied physical-work summary")
    border_ticks = (
        None
        if border is None
        else (4 * border.get("3_reentries", 0) + border.get("zero_tail_symbols", 0))
    )
    return {
        "macro": macro,
        "conditional_physical_ticks": None
        if conditional is None
        else conditional.get("physical_ticks", 0),
        "border_actions": action_count,
        "border_macro_physical_ticks": border_ticks,
        "mixed_macro_actions": None if mixed is None else mixed.get("actions", 0),
        "mixed_macro_repetitions": None
        if mixed is None
        else mixed.get("repetitions", 0),
        "mixed_macro_physical_ticks": None
        if mixed is None
        else mixed.get("physical_ticks", 0),
    }, execution


def _sample(
    mode: Mode,
    trial: int,
    source: int,
    ticks: int,
    expected: int,
) -> Sample:
    NumberCompiler.clear_shared_cache()
    arguments = _run_arguments(source, ticks)
    context = (
        nullcontext()
        if mode == "enabled"
        else selector_ablation(include_mixed=mode == "all_selectors_disabled")
    )
    try:
        with context:
            elapsed, packet = cli_sample(arguments, fresh=False)
    finally:
        NumberCompiler.clear_shared_cache()
    raw_value = packet.get("value")
    if not isinstance(raw_value, str) or raw_value != str(expected):
        raise AssertionError("public Collatz CLI differs from literal physical steps")
    observed, execution_metrics = packets(packet)
    return Sample(
        mode=mode,
        trial=trial,
        seconds=elapsed,
        value=raw_value,
        border_actions=observed["border_actions"],
        border_macro_physical_ticks=observed["border_macro_physical_ticks"],
        conditional_physical_ticks=observed["conditional_physical_ticks"],
        mixed_macro_actions=observed["mixed_macro_actions"],
        mixed_macro_repetitions=observed["mixed_macro_repetitions"],
        mixed_macro_physical_ticks=observed["mixed_macro_physical_ticks"],
        macro=observed["macro"],
        execution_metrics=execution_metrics,
    )


def compare(
    motif: tuple[int, ...],
    groups: int,
    trials: int,
    *,
    on_sample: Callable[[Sample], None] | None = None,
) -> dict[str, object]:
    if type(trials) is not int or trials < 1:
        raise ValueError("trial count must be positive")
    source = source_for(motif, groups)
    if source.bit_length() > 4096:
        raise ValueError("constructed source exceeds the benchmark output-size cap")
    ring = PeriodicTail6305Ring.from_source(source, motif)
    if not ring.admits(groups):
        raise ValueError("constructed motif is not admitted for all requested groups")
    ticks = groups * ring.physical_ticks
    if ticks > 4096:
        raise ValueError("ablation workload exceeds the 4096-tick scalar reference cap")
    expected = collatz_literal(source, ticks)
    if ring.endpoint(groups) != expected:
        raise ArithmeticError("6305 ring endpoint differs from literal physical steps")
    require_macro = ticks > 64 and groups >= 3 and ring.admits(3)

    samples: list[Sample] = []
    for trial in range(trials):
        mode_orders: tuple[tuple[Mode, Mode, Mode], ...] = (
            ("enabled", "selector_disabled", "all_selectors_disabled"),
            ("selector_disabled", "all_selectors_disabled", "enabled"),
            ("all_selectors_disabled", "enabled", "selector_disabled"),
        )
        modes = mode_orders[trial % len(mode_orders)]
        for mode in modes:
            sample = _sample(
                mode,
                trial,
                source,
                ticks,
                expected,
            )
            samples.append(sample)
            if on_sample is not None:
                on_sample(sample)
    enabled = [row for row in samples if row["mode"] == "enabled"]
    disabled = [row for row in samples if row["mode"] == "selector_disabled"]
    fallback = [row for row in samples if row["mode"] == "all_selectors_disabled"]
    if not enabled or (
        require_macro
        and any(
            (row["conditional_physical_ticks"] or 0)
            + (row["mixed_macro_physical_ticks"] or 0)
            + (row["border_macro_physical_ticks"] or 0)
            < ticks - 64
            for row in enabled
        )
    ):
        raise AssertionError(
            "enabled CLI query did not consume a complete powered action"
        )
    if any(row["border_actions"] for row in disabled):
        raise AssertionError("disabled CLI query still consumed a 6305R action")
    if any(
        row["border_actions"]
        or (row["conditional_physical_ticks"] or 0)
        or (row["mixed_macro_actions"] or 0)
        or (row["mixed_macro_physical_ticks"] or 0)
        for row in fallback
    ):
        raise AssertionError(
            "selector-disabled CLI query still consumed a named or mixed macro"
        )
    enabled_seconds = statistics.median(row["seconds"] for row in enabled)
    disabled_seconds = statistics.median(row["seconds"] for row in disabled)
    fallback_seconds = statistics.median(row["seconds"] for row in fallback)
    output_upper_bound = (source + 1) * 3**ticks
    return {
        "scope": (
            "same-source public CLI query; independent literal physical endpoint reference; "
            "the named-only mode ablates 6305 selection; the full fallback mode "
            "also ablates conditional and mixed-clock selection. Exact fallback execution is kept, "
            "and consumed mixed-action and border-action work comes from "
            "schema-eight execution metrics; "
            "timings include output"
        ),
        "source": source,
        "source_bits": source.bit_length(),
        "source_and_ring_construction_timing": "excluded from CLI samples",
        "literal_reference_timing": "excluded from CLI samples",
        "query_execution": "same-process public CLI; shared caches cleared before every sample",
        "motif": motif,
        "groups": groups,
        "physical_ticks": ticks,
        "expected_endpoint": expected,
        "expected_endpoint_decimal_digits": len(str(expected)),
        "safe_output_digit_bound": len(str(output_upper_bound)),
        "ring_capacity": ring.return_capacity,
        "powered_action_exercised": require_macro,
        "enabled_consumed_powered_physical_ticks": [
            (row["conditional_physical_ticks"] or 0)
            + (row["mixed_macro_physical_ticks"] or 0)
            + (row["border_macro_physical_ticks"] or 0)
            for row in enabled
        ],
        "enabled_consumed_named_border_actions": [
            row["border_actions"] for row in enabled
        ],
        "selector_disabled_consumed_mixed_clock_actions": [
            row["mixed_macro_actions"] for row in disabled
        ],
        "selector_disabled_consumed_mixed_clock_physical_ticks": [
            row["mixed_macro_physical_ticks"] for row in disabled
        ],
        "fallback_consumed_border_actions": [row["border_actions"] for row in fallback],
        "fallback_consumed_mixed_clock_actions": [
            row["mixed_macro_actions"] for row in fallback
        ],
        "fallback_consumed_mixed_clock_physical_ticks": [
            row["mixed_macro_physical_ticks"] for row in fallback
        ],
        "named_6305_selector_improves_this_source": any(
            row["border_actions"] for row in enabled
        )
        and not any(row["border_actions"] for row in disabled),
        "macro_enabled_median_seconds": enabled_seconds,
        "selector_disabled_median_seconds": disabled_seconds,
        "all_selectors_disabled_median_seconds": fallback_seconds,
        "selector_disabled_over_enabled_time_ratio": (
            disabled_seconds / enabled_seconds if enabled_seconds else None
        ),
        "all_selectors_disabled_over_enabled_time_ratio": (
            fallback_seconds / enabled_seconds if enabled_seconds else None
        ),
        "samples": samples,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--motif", type=int, nargs="+", default=[1, 2])
    parser.add_argument("--groups", type=int, default=12)
    parser.add_argument("--trials", type=int, default=5)
    options = parser.parse_args()
    motif = tuple(options.motif)
    scope = (
        "same-source public CLI query; exact literal physical endpoint reference; "
        "named-only and all-selector ablations retain exact fallback; consumed "
        "actions are recorded in schema-eight execution metrics"
    )
    configuration: dict[str, object] = {
        "motif": motif,
        "groups": options.groups,
        "trials": options.trials,
    }

    def run(on_sample: Callable[[Sample], None]) -> dict[str, object]:
        return compare(
            motif,
            options.groups,
            options.trials,
            on_sample=on_sample,
        )

    return run_jsonl_report(
        "devtools.benchmarks.collatz_border_macro_ablation",
        "comparison.json",
        scope,
        configuration,
        run,
        run_metadata={
            "source_and_ring_construction_timing": "excluded from CLI samples",
            "literal_reference_timing": "excluded from CLI samples",
            "query_execution": (
                "same-process public CLI; shared caches cleared before every sample"
            ),
        },
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
