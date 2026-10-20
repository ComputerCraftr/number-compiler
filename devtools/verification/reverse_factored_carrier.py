"""Bounded independent validation and per-plane measurements of the carrier."""

from __future__ import annotations

import argparse
import json
from itertools import product
from pathlib import Path
from time import perf_counter
from typing import Never
from unittest.mock import patch

from devtools.experiments.reverse_add.cocycle_carrier import CocycleReverseCarrier
from devtools.experiments.reverse_add.factored_carrier import (
    FactoredReverseCarrier,
)
from devtools.experiments.reverse_add.factored_power import FactoredTemporalPower
from devtools.verification import exact_oracle, require_exact_oracle
from devtools.verification.reverse_plane_checkpoint import export_planes, import_planes
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_crt_digit,
)


def native_macro(seed: int, steps: int) -> dict[str, object]:
    """Measure one source-only J4 square, separating construction from output.

    Run this mode in a fresh process for each cold sample: plane-word interning
    is process-wide. A same-instance repeat is reported separately, never as
    cold discovery. Literal validation happens only after construction.
    """
    require_exact_oracle()
    if type(seed) is not int or seed < 0 or type(steps) is not int or steps < 1:
        raise ValueError("native macro needs a nonnegative seed and positive extent")
    carrier = CocycleReverseCarrier()
    started = perf_counter()
    source = carrier.source(reverse_pair_sums(seed, 10))
    discovery_seconds = perf_counter() - started
    power = FactoredTemporalPower(carrier)
    discovered_work = carrier.planes.total_work
    with (
        patch.object(
            carrier, "source", side_effect=AssertionError("re-encoded source")
        ),
        patch.object(carrier, "decode", side_effect=AssertionError("decoded endpoint")),
        patch.object(
            carrier.planes, "from_values", side_effect=AssertionError("imported rows")
        ),
    ):
        started = perf_counter()
        block = power.block(source, steps)
        construction_seconds = perf_counter() - started
        constructed_work = carrier.planes.total_work
        started = perf_counter()
        if power.block(source, steps) is not block:
            raise AssertionError("warm macro did not reuse the admitted block")
        warm_seconds = perf_counter() - started
    if block.emission is None:
        raise AssertionError("positive macro lost its terminal output channels")
    alpha, epsilon = block.emission
    started = perf_counter()
    width = carrier.planes.resolve(alpha).length
    digits = [
        decimal_crt_digit(
            carrier.planes.atom(alpha, i), carrier.planes.atom(epsilon, i)
        )
        for i in reversed(range(width))
    ]
    value = "".join(map(str, digits))
    rendering_seconds = perf_counter() - started
    expected = seed
    for _ in range(steps):
        expected += int(str(expected)[::-1])
    if value != str(expected):
        raise AssertionError("terminal output differs from bounded literal reference")
    return {
        "seed": seed,
        "steps": steps,
        "value": value,
        "discovery_seconds": discovery_seconds,
        "construction_seconds": construction_seconds,
        "warm_seconds": warm_seconds,
        "rendering_seconds": rendering_seconds,
        "discovery_work": discovered_work,
        "construction_work": constructed_work - discovered_work,
        "total_plane_work": carrier.planes.total_work,
        "gate_cache_hits": carrier.planes.gate_cache_hits,
        "cofactor_cells": carrier.planes.cofactor_cells,
        "cofactor_hits": carrier.planes.cofactor_hits,
        "cofactor_entries": carrier.planes.audit_snapshot().cofactor_entries,
        "cofactor_table_cells": carrier.planes.cofactor_table_cells,
        "cofactor_evictions": carrier.planes.cofactor_evictions,
        "projection_returns": carrier.planes.projection_returns,
        "constant_returns": carrier.planes.constant_returns,
        "memo_prune_visits": carrier.planes.memo_prune_visits,
        "reuse_lookups": carrier.planes.reuse_lookups,
        "reuse_hits": carrier.planes.reuse_hits,
        "reuse_evictions": carrier.planes.reuse_evictions,
        "reuse_peak_entries": carrier.planes.reuse_peak_entries,
        "macro_cache_hits": power.cache_hits,
        "compositions": power.compositions,
        "carrier": carrier.metrics(block.output),
        "production_admitted": False,
        "temporal_compression_proved": False,
    }


def _forbidden_pair_reconstruction(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("successor decoded or re-encoded a pair word")


def exhaustive(
    width: int, first: int | None = None, limit: int | None = None
) -> dict[str, object]:
    require_exact_oracle()
    if type(width) is not int or not 1 <= width <= 8:
        raise ValueError("exhaustive widths are one through eight")
    axes = [range(19)] * (width // 2)
    if width % 2:
        axes.append(range(0, 19, 2))
    if first is not None:
        if first not in axes[0]:
            raise ValueError("first coefficient is outside this width's universe")
        axes[0] = range(first, first + 1)
    carrier = FactoredReverseCarrier()
    encode, decode = carrier.source, carrier.decode
    count = 0
    started = perf_counter()
    # The same poison applies to every successor. Keep the original bound
    # methods solely for independent input/output checks, avoiding two fresh
    # MagicMocks and exception objects for each member of the finite universe.
    with (
        patch.object(carrier, "decode", _forbidden_pair_reconstruction),
        patch.object(carrier, "source", _forbidden_pair_reconstruction),
    ):
        for half in product(*axes):
            field = half + (half[:-1] if width % 2 else half)[::-1]
            q = encode(field)
            expected, growth = pair_step(field, 10)
            out, observed_growth = carrier.successor(q)
            observed = decode(out)
            if observed != expected or observed_growth != growth:
                raise AssertionError((field, expected, observed))
            count += 1
            if limit is not None and count >= limit:
                break
    return {
        "width": width,
        "first": first,
        "cases": count,
        "seconds": perf_counter() - started,
        "complete_partition": limit is None,
    }


def trajectory(
    seed: int,
    steps: int,
    *,
    squaring: bool = False,
    resume: Path | None = None,
    checkpoint: Path | None = None,
) -> dict[str, object]:
    require_exact_oracle()
    field = reverse_pair_sums(seed, 10)
    carrier = FactoredReverseCarrier()
    source = carrier.source(field)
    start = 0
    earlier_seconds = 0.0
    if resume is not None:
        archive = json.loads(resume.read_text())
        if archive["seed"] != seed or squaring:
            raise ValueError(
                "checkpoint seed mismatch or unsupported power-cache resume"
            )
        start = archive["event"]
        earlier_seconds = archive["seconds"]
        if type(start) is not int or not 0 <= start < steps:
            raise ValueError("checkpoint event is outside the requested interval")
        source = import_planes(carrier, archive["planes"])
        for _ in range(start):
            field, _ = pair_step(field, 10)
        if carrier.decode(source) != field:
            raise AssertionError(
                "checkpoint disagrees with its independent source orbit"
            )
    cell = source
    power = FactoredTemporalPower(carrier)
    rows: list[dict[str, object]] = []
    started = perf_counter()
    outputs: set[object] = set()
    checkpoints = {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, steps}
    for event in range(start + 1, steps + 1):
        field, _ = pair_step(field, 10)
        if squaring:
            if event not in checkpoints:
                continue
            cell = power.advance(source, event)
        else:
            cell, _ = carrier.successor(cell)
        if carrier.decode(cell) != field:
            raise AssertionError((seed, event))
        if event in checkpoints:
            outputs.add(carrier.residual(cell))
            affine_metrics: dict[str, object] = {}
            if squaring:
                action = power.block(source, event).action
                affine_metrics = {
                    "f5_homogeneous_growths": action.linear.growths,
                    "f5_frobenius_factors": action.linear.frobenius_factors(),
                    "f5_forcing_nodes": carrier.planes.metrics(action.forcing)["nodes"],
                }
            rows.append(
                {
                    "event": event,
                    **carrier.metrics(cell),
                    **affine_metrics,
                    "observed_output_residuals": len(outputs),
                    "primitive_successors": start + carrier.successor_evaluations,
                    "power_cache_hits": power.cache_hits,
                    "seconds": earlier_seconds + perf_counter() - started,
                }
            )
            print(json.dumps({"checkpoint": rows[-1]}), flush=True)
    elapsed = earlier_seconds + perf_counter() - started
    if checkpoint is not None:
        checkpoint.write_text(
            json.dumps(
                {
                    "seed": seed,
                    "event": steps,
                    "seconds": elapsed,
                    "planes": export_planes(carrier, cell),
                }
            )
        )
    return {
        "seed": seed,
        "steps": steps,
        "squaring": squaring,
        "rows": rows,
        "seconds": elapsed,
        "resumed_at": start,
    }


def uniform(width: int) -> dict[str, object]:
    carrier = FactoredReverseCarrier()
    cell = carrier.uniform(CarryFn.CONST0, 2, 0, width)
    rows = [carrier.metrics(cell)]
    with (
        patch.object(
            carrier, "decode", side_effect=AssertionError("uniform expansion")
        ),
        patch.object(
            carrier, "source", side_effect=AssertionError("uniform re-encoding")
        ),
    ):
        for _ in range(4):
            cell, _ = carrier.successor(cell)
            rows.append(carrier.metrics(cell))
    p = carrier.planes
    assert p.atom(cell.domain, 0) == p.atom(cell.domain, width) == 0
    assert p.atom(cell.f5, 0) == p.atom(cell.f5, width) == 2
    assert p.atom(cell.half, 0) == p.atom(cell.half, width) == 1
    if width > 1:
        assert p.atom(cell.domain, width // 2) == 2
        assert p.atom(cell.f5, width // 2) == 4
        assert p.atom(cell.half, width // 2) == 0
    return {"width": width, "rows": rows}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "mode", choices=("exhaustive", "trajectory", "uniform", "native-macro")
    )
    parser.add_argument("--width", type=int, default=4)
    parser.add_argument("--first", type=int)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--seed", type=int, default=196)
    parser.add_argument("--steps", type=int, default=16)
    parser.add_argument("--squaring", action="store_true")
    parser.add_argument("--resume", type=Path)
    parser.add_argument("--checkpoint", type=Path)
    args = parser.parse_args()
    with exact_oracle():
        if args.mode == "exhaustive":
            result = exhaustive(args.width, args.first, args.limit)
        elif args.mode == "trajectory":
            result = trajectory(
                args.seed,
                args.steps,
                squaring=args.squaring,
                resume=args.resume,
                checkpoint=args.checkpoint,
            )
        elif args.mode == "native-macro":
            result = native_macro(args.seed, args.steps)
        else:
            result = uniform(args.width)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
