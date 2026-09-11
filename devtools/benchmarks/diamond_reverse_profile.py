"""Capped cold measurements of the executable reverse diamond candidate.

This exercises the public generic index with the exact compiled arithmetic
operator. Certified reverse term routing is reported separately; this diagnostic
must not be described as evidence that the family cutover has been completed.
"""

from __future__ import annotations

import argparse
import json
import resource
import signal
import sys
from dataclasses import asdict
from time import perf_counter, process_time

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.compilation import compile_reverse_pair_power


def _expired(signum: object, frame: object) -> None:
    raise TimeoutError("fixed diagnostic watchdog expired")


def profile(steps: int, cap: int, *, width: bool = False) -> dict[str, object]:
    if steps < 1 or cap < 0:
        raise ValueError("positive exponent and nonnegative cache cap required")
    ledger = ResourceLedger(max_cache_entries=cap)
    compiler = LazyCompiler(ledger)
    power = compile_reverse_pair_power(compiler, 10, steps - 1)
    terminal = compiler.atom(DigitNormalizeBlockEffect(10))
    effect = terminal if power.root is None else compiler.compose(power.root, terminal)
    construction_start = perf_counter()
    index = HashLifeBlockIndex(
        effect, (7, 18, 7), logical_length=3 + steps, ledger=ledger, compiler=compiler
    )
    construction_seconds = perf_counter() - construction_start
    phases = {}
    old_handler = signal.signal(signal.SIGALRM, _expired)
    requests = [("point", 0), ("warm_point", 0)] + ([("width", None)] if width else [])
    status = "complete"
    try:
        for name, coordinate in requests:
            # The bounded response register cannot supply the warm observation.
            index._point_response.clear()
            start, cpu = perf_counter(), process_time()
            signal.alarm(40)
            value = None
            try:
                value = (
                    index.direct_active_width()
                    if coordinate is None
                    else index.direct_powered_point(coordinate)
                )
            except BlockContextBudgetExceeded:
                status = "resource-cap"
            except TimeoutError:
                status = "watchdog"
            finally:
                signal.alarm(0)
            seconds, cpu_seconds = perf_counter() - start, process_time() - cpu
            metrics_start = perf_counter()
            measured = asdict(index.metrics())
            measured.pop("resource_inventory")
            phases[name] = {
                "status": status,
                "value": value,
                "seconds": seconds,
                "cpu_seconds": cpu_seconds,
                "metrics_snapshot_seconds": perf_counter() - metrics_start,
                "metrics": measured,
            }
            if status != "complete":
                break
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)
    # This exact integer is solely a post-measurement oracle. It never supplies
    # a carry, branch, width, or digit to the executable program.
    expected = 196
    for _ in range(steps):
        expected += int(str(expected)[::-1])
    if phases["point"]["value"] is not None:
        assert phases["point"]["value"] == expected % 10
    if "warm_point" in phases and phases["warm_point"]["value"] is not None:
        assert phases["warm_point"]["value"] == expected % 10
    if "width" in phases and phases["width"]["value"] is not None:
        assert phases["width"]["value"] == len(str(expected))
    return {
        "family": "reverse-diamond-candidate",
        "source": 196,
        "steps": steps,
        "public_certified_family_cutover": False,
        "cache_cap": cap,
        "watchdog_seconds_per_phase": 40,
        "construction_seconds": construction_seconds,
        "status": status,
        "phases": phases,
        "process_peak_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        * (1 if sys.platform == "darwin" else 1024),
        "inventory": [asdict(row) for row in ledger.inventory()],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, required=True)
    parser.add_argument("--cap", type=int, default=180000)
    parser.add_argument("--width", action="store_true")
    options = parser.parse_args()
    print(
        json.dumps(
            profile(options.steps, options.cap, width=options.width), sort_keys=True
        )
    )
