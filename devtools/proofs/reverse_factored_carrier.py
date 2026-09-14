"""Bounded independent validation and per-plane measurements of the carrier."""

from __future__ import annotations

import argparse
import json
from itertools import product
from pathlib import Path
from time import perf_counter
from unittest.mock import patch

from devtools.proofs import exact_oracle, require_exact_oracle
from devtools.proofs.reverse_plane_checkpoint import export_planes, import_planes
from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.sequences.reverse_add.factored_carrier import (
    FactoredReverseCarrier,
)
from number_compiler.sequences.reverse_add.factored_power import FactoredTemporalPower


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
    count = 0
    started = perf_counter()
    for half in product(*axes):
        field = half + (half[:-1] if width % 2 else half)[::-1]
        q = carrier.source(field)
        expected, growth = pair_step(field, 10)
        with (
            patch.object(
                carrier,
                "decode",
                side_effect=AssertionError("successor decoded a pair word"),
            ),
            patch.object(
                carrier,
                "source",
                side_effect=AssertionError("successor re-encoded a pair word"),
            ),
        ):
            out, observed_growth = carrier.successor(q)
        if carrier.decode(out) != expected or observed_growth != growth:
            raise AssertionError((field, expected, carrier.decode(out)))
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
    rows = []
    started = perf_counter()
    outputs = set()
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
    parser.add_argument("mode", choices=("exhaustive", "trajectory", "uniform"))
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
        else:
            result = uniform(args.width)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
