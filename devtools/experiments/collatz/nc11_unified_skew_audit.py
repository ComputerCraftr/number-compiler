"""Finite-run differential and enabled/bypassed work audit for Collatz skew joins.

All checks concern exact finite prefixes. The comparison bypasses only the
new composer at its executor boundary; the ordinary selectors remain active.
"""

from __future__ import annotations

import argparse
import json
import random
import statistics
import time
from typing import Any
from unittest.mock import patch

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.innovation_carry_cocycle import (
    exact_source_symbol,
)
from number_compiler.sequences.collatz.innovation_port_moore import SIGNED_SYMBOLS
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)
from tests.support.collatz_finite_trace import normalized_trace, physical_values


def _require(condition: bool, detail: object) -> None:
    if not condition:
        raise AssertionError(detail)


def audit(samples: int = 2000, seed: int = 1116305) -> dict[str, int]:
    rng = random.Random(seed)
    fused = terminal = nonterminal = 0
    for i in range(samples):
        # Cover fixed border fibers, upper-border lifts, and fresh mixed words.
        base = (13, 23, 26, 30, 43, 190, 2174, 27, 112, 592, 2, 5)[i % 12]
        if i % 5 == 0:
            source = base
        elif i % 5 == 1:
            source = base + (1 << rng.randrange(12, 200))
        elif i % 5 == 2:
            source = rng.randrange(1, 1 << rng.randrange(4, 110))
        elif i % 5 == 3:
            source = base + 160 * rng.randrange(1, 1 << 15)
        else:
            source = (rng.randrange(1, 1 << 20) << 32) + base
        ticks = rng.randrange(0, 145)
        physical = physical_values(source, ticks)
        ledger = ResourceLedger()
        result = compile_collatz_temporal_run_quotient(
            source,
            ticks,
            ledger=ledger,
            include_joint_cocycle=True,
            include_width_spine=True,
            include_f5=True,
            include_innovation_tape=True,
            innovation_modulus=49,
            shared_cache=False,
        )
        _require(result.endpoint == physical[-1], (i, source, ticks, "endpoint"))
        _require(result.odd_ticks + result.division_ticks == ticks, (i, "clocks"))
        starts, normalized_end = normalized_trace(source, result.normalized_symbols)
        expected_normalized_endpoint = (
            result.endpoint if result.phase == 0 else (result.endpoint - 1) // 3
        )
        _require(
            normalized_end == expected_normalized_endpoint,
            (i, source, ticks, "phase"),
        )
        width_summary = result.tape_width_summary
        if width_summary is None:
            raise AssertionError((i, "missing width summary"))
        width = width_summary.blank
        _require(
            source.bit_length() + width.minimum == min(map(int.bit_length, physical)),
            (i, "minimum width"),
        )
        _require(
            source.bit_length() + width.maximum == max(map(int.bit_length, physical)),
            (i, "maximum width"),
        )
        physical_f5 = result.physical_f5
        if physical_f5 is None:
            raise AssertionError((i, "missing physical F5"))
        _require(physical_f5.apply(source) == physical[-1] % 5, (i, "F5"))
        accumulator = result.accumulator(49)
        normsum = source + sum(
            (3 * value + 1) // 2 if value & 1 else value // 2 for value in starts
        )
        _require(
            accumulator.normalized_accumulator_residue == normsum % 49,
            (i, "normalized accumulator"),
        )
        observed = result.innovation_observation
        if observed is None:
            raise AssertionError((i, "missing innovation observation"))
        expected = tuple(exact_source_symbol(value, 49) for value in starts)
        expected_counts = tuple(expected.count(symbol) for symbol in SIGNED_SYMBOLS)
        _require(tuple(observed.symbol_counts) == expected_counts, (i, "tape counts"))
        _require(
            tuple(observed.sample) == expected[: len(observed.sample)],
            (i, "tape sample"),
        )
        chain = result.unified_skew_chain
        if chain is not None:
            chain.verify()
            _require(chain.source == source, (i, "chain source"))
            _require(chain.physical_ticks <= ticks, (i, "chain horizon"))
            if chain.clock is not None:
                _require(
                    chain.clock.physical_ticks == chain.physical_ticks,
                    (i, "chain physical clock"),
                )
                _require(
                    chain.clock.steps == chain.normalized_symbols,
                    (i, "chain normalized clock"),
                )
            fused += 1
            if chain.reaches_terminal:
                terminal += 1
            else:
                nonterminal += 1
    return {
        "samples": samples,
        "seed": seed,
        "independent_physical_matches": samples,
        "independent_width_f5_accumulator_signed_tape_matches": samples,
        "joined_prefixes": fused,
        "joined_terminal_paths": terminal,
        "joined_live_prefixes": nonterminal,
    }


_FIXED_SOURCES = (13, 23, 30, 2174, 190, 27)
_FIXED_HORIZONS = (16, 32, 64, 128, 256, 512, 1024)
_MEASURED_COUNTER_PARTS = (
    "unified_skew",
    "boundary_",
    "border_return",
    "dyadic_d8",
    "selector",
    "discovery",
    "run_actions",
    "operand_bits",
    "macro_actions",
    "cache_",
)


def _measured_counters(ledger: ResourceLedger) -> dict[str, int]:
    return {
        name: value
        for name, value in sorted(ledger.counters.items())
        if any(part in name for part in _MEASURED_COUNTER_PARTS)
    }


def _compile_comparison_case(
    source: int, ticks: int, *, enabled: bool
) -> tuple[dict[str, Any], float]:
    ledger = ResourceLedger()
    start = time.perf_counter()
    if enabled:
        result = compile_collatz_temporal_run_quotient(
            source,
            ticks,
            ledger=ledger,
            shared_cache=False,
            include_joint_cocycle=True,
            include_width_spine=True,
            include_f5=True,
            include_innovation_tape=True,
            innovation_modulus=49,
        )
    else:
        with patch(
            "number_compiler.sequences.collatz.temporal_run_executor."
            "consume_unified_skew_chain",
            return_value=None,
        ):
            result = compile_collatz_temporal_run_quotient(
                source,
                ticks,
                ledger=ledger,
                shared_cache=False,
                include_joint_cocycle=True,
                include_width_spine=True,
                include_f5=True,
                include_innovation_tape=True,
                innovation_modulus=49,
            )
    elapsed = time.perf_counter() - start
    chain = result.unified_skew_chain
    return (
        {
            "endpoint": result.endpoint,
            "normalized_symbols": result.normalized_symbols,
            "phase": result.phase,
            "odd_ticks": result.odd_ticks,
            "division_ticks": result.division_ticks,
            "run_actions": result.run_actions,
            "joined_prefix_ticks": chain.physical_ticks if chain is not None else 0,
            "joined_segments": len(chain.segment_identities)
            if chain is not None
            else 0,
            "counters": _measured_counters(ledger),
        },
        elapsed,
    )


def compare_enabled_bypassed(trials: int = 5) -> dict[str, Any]:
    if type(trials) is not int or trials < 1:
        raise ValueError("comparison trials must be positive")
    cases: list[dict[str, Any]] = []
    for source in _FIXED_SOURCES:
        for ticks in _FIXED_HORIZONS:
            observations: dict[str, list[dict[str, Any]]] = {
                "enabled": [],
                "bypassed": [],
            }
            durations: dict[str, list[float]] = {"enabled": [], "bypassed": []}
            for trial in range(trials):
                order = (
                    ("enabled", "bypassed")
                    if trial % 2 == 0
                    else (
                        "bypassed",
                        "enabled",
                    )
                )
                for mode in order:
                    result, elapsed = _compile_comparison_case(
                        source, ticks, enabled=mode == "enabled"
                    )
                    observations[mode].append(result)
                    durations[mode].append(elapsed)
            enabled_results = observations["enabled"]
            bypassed_results = observations["bypassed"]
            expected = (
                enabled_results[0]["endpoint"],
                enabled_results[0]["normalized_symbols"],
                enabled_results[0]["phase"],
                enabled_results[0]["odd_ticks"],
                enabled_results[0]["division_ticks"],
            )
            for observed in (*enabled_results, *bypassed_results):
                actual = (
                    observed["endpoint"],
                    observed["normalized_symbols"],
                    observed["phase"],
                    observed["odd_ticks"],
                    observed["division_ticks"],
                )
                _require(
                    actual == expected,
                    (source, ticks, "mode semantic mismatch", actual, expected),
                )
            counter_names = sorted(
                set().union(
                    *(
                        set(observed["counters"])
                        for observed in (*enabled_results, *bypassed_results)
                    )
                )
            )
            median_counters = {
                mode: {
                    name: int(
                        statistics.median(
                            observed["counters"].get(name, 0)
                            for observed in observations[mode]
                        )
                    )
                    for name in counter_names
                }
                for mode in ("enabled", "bypassed")
            }
            cases.append(
                {
                    "source": source,
                    "ticks": ticks,
                    "trials": trials,
                    "semantics": {
                        "endpoint": expected[0],
                        "normalized_symbols": expected[1],
                        "phase": expected[2],
                    },
                    "median": {
                        mode: {
                            "seconds": statistics.median(durations[mode]),
                            "run_actions": int(
                                statistics.median(
                                    int(item["run_actions"])
                                    for item in observations[mode]
                                )
                            ),
                            "joined_prefix_ticks": int(
                                statistics.median(
                                    int(item["joined_prefix_ticks"])
                                    for item in observations[mode]
                                )
                            ),
                            "joined_segments": int(
                                statistics.median(
                                    int(item["joined_segments"])
                                    for item in observations[mode]
                                )
                            ),
                            "counters": median_counters[mode],
                        }
                        for mode in ("enabled", "bypassed")
                    },
                }
            )
    return {"trials": trials, "cases": cases}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=1116305)
    parser.add_argument("--compare", action="store_true")
    parser.add_argument("--comparison-trials", type=int, default=5)
    args = parser.parse_args()
    output: dict[str, Any] = {}
    if args.samples:
        output["finite_audit"] = audit(args.samples, args.seed)
    if args.compare:
        output["enabled_vs_bypassed"] = compare_enabled_bypassed(args.comparison_trials)
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
