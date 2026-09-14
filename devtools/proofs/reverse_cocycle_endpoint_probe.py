"""Measure the primitive parity endpoint carrier at bounded 196 milestones.

This is an explicit endpoint diagnostic.  It advances one primitive cocycle
successor per event and reports the retained Gamma/domain, F5, and epsilon
plane DAGs.  It deliberately does not use temporal powering or publish a
powered quotient.  Use ``--chunk`` with a checkpoint to keep guarded runs
bounded, for example:

    python -m devtools.proofs.reverse_cocycle_endpoint_probe \
        --steps 1024 --chunk 128 --checkpoint /tmp/reverse-196.json
    python -m devtools.proofs.reverse_cocycle_endpoint_probe \
        --steps 1024 --chunk 128 --resume /tmp/reverse-196.json \
        --checkpoint /tmp/reverse-196.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from time import perf_counter

from devtools.proofs import exact_oracle, require_exact_oracle
from devtools.proofs.reverse_plane_checkpoint import (
    export_plane_roots,
    import_plane_roots,
)
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.sequences.reverse_add.cocycle_carrier import (
    CocycleCell,
    CocycleReverseCarrier,
)

MILESTONES = frozenset((16, 32, 64, 128, 256, 512, 1024))


def _plane_metrics(
    carrier: CocycleReverseCarrier, cell: CocycleCell
) -> dict[str, dict[str, int]]:
    """Return named channel DAG metrics without reading represented cells."""
    return {
        "gamma": carrier.planes.metrics(cell.domain),
        "f5": carrier.planes.metrics(cell.f5),
        "epsilon": carrier.planes.metrics(cell.epsilon),
    }


def _row(
    carrier: CocycleReverseCarrier,
    cell: CocycleCell,
    event: int,
    *,
    primitive_before: int,
    nonlinear_before: int,
    seconds: float,
) -> dict[str, object]:
    planes = _plane_metrics(carrier, cell)
    dag_nodes = sum(int(metrics["nodes"]) for metrics in planes.values())
    dag_references = sum(int(metrics["references"]) for metrics in planes.values())
    return {
        "event": event,
        "width": carrier.planes.resolve(cell.domain, "domain").length,
        "planes": planes,
        "plane_dag_nodes": dag_nodes,
        "plane_dag_references": dag_references,
        "primitive_successors": primitive_before + carrier.primitive_successors,
        "primitive_successors_in_chunk": carrier.primitive_successors,
        "nonlinear_gate_requests": nonlinear_before + carrier.nonlinear_gate_requests,
        "nonlinear_gate_requests_in_chunk": carrier.nonlinear_gate_requests,
        "seconds": seconds,
    }


def _load_checkpoint(
    carrier: CocycleReverseCarrier,
    archive_path: Path,
    *,
    seed: int,
    target: int,
) -> tuple[CocycleCell, int, int, int, float]:
    archive = json.loads(archive_path.read_text())
    if (
        type(archive) is not dict
        or archive.get("format") != "reverse-cocycle-endpoint-v1"
    ):
        raise ValueError("checkpoint has another format")
    if archive.get("seed") != seed:
        raise ValueError("checkpoint seed mismatch")
    start = archive.get("event")
    if type(start) is not int or start < 0 or start > target:
        raise ValueError("checkpoint event is outside the requested interval")
    primitive = archive.get("primitive_successors", start)
    nonlinear = archive.get("nonlinear_gate_requests", 2 * start)
    seconds = archive.get("seconds", 0.0)
    if (
        type(primitive) is not int
        or primitive != start
        or type(nonlinear) is not int
        or nonlinear != 2 * start
        or type(seconds) not in (int, float)
        or seconds < 0
    ):
        raise ValueError("checkpoint counters are invalid")
    roots = import_plane_roots(carrier, archive["planes"])
    cell = CocycleCell(*roots)
    carrier.validate(cell)
    return cell, start, primitive, nonlinear, float(seconds)


def probe(
    seed: int,
    steps: int,
    *,
    chunk: int | None = None,
    resume: Path | None = None,
    checkpoint: Path | None = None,
) -> dict[str, object]:
    """Advance through one bounded primitive chunk and emit milestone rows."""
    require_exact_oracle()
    if type(seed) is not int or seed < 0:
        raise ValueError("seed must be a nonnegative integer")
    if type(steps) is not int or steps < 0:
        raise ValueError("steps must be a nonnegative integer")
    if chunk is not None and (type(chunk) is not int or chunk < 1):
        raise ValueError("chunk must be a positive integer")

    carrier = CocycleReverseCarrier()
    field = reverse_pair_sums(seed, 10)
    if resume is None:
        cell = carrier.source(field)
        start = 0
        primitive_before = nonlinear_before = 0
        earlier_seconds = 0.0
    else:
        cell, start, primitive_before, nonlinear_before, earlier_seconds = (
            _load_checkpoint(carrier, resume, seed=seed, target=steps)
        )
        for _ in range(start):
            field, _ = pair_step(field, 10)
        if carrier.decode(cell) != field:
            raise AssertionError(
                "checkpoint disagrees with its independent source orbit"
            )

    stop = steps if chunk is None else min(steps, start + chunk)
    rows: list[dict[str, object]] = []
    started = perf_counter()
    for event in range(start + 1, stop + 1):
        field, expected_growth = pair_step(field, 10)
        cell, observed_growth = carrier.successor(cell)
        if observed_growth != expected_growth or carrier.decode(cell) != field:
            raise AssertionError((seed, event, observed_growth, expected_growth))
        if event in MILESTONES or event == stop:
            row = _row(
                carrier,
                cell,
                event,
                primitive_before=primitive_before,
                nonlinear_before=nonlinear_before,
                seconds=earlier_seconds + perf_counter() - started,
            )
            rows.append(row)
            print(json.dumps({"checkpoint": row}), flush=True)

    elapsed = earlier_seconds + perf_counter() - started
    if checkpoint is not None:
        checkpoint.write_text(
            json.dumps(
                {
                    "format": "reverse-cocycle-endpoint-v1",
                    "seed": seed,
                    "event": stop,
                    "seconds": elapsed,
                    "primitive_successors": primitive_before
                    + carrier.primitive_successors,
                    "nonlinear_gate_requests": nonlinear_before
                    + carrier.nonlinear_gate_requests,
                    "planes": export_plane_roots(
                        carrier,
                        (cell.domain, cell.f5, cell.epsilon),
                    ),
                }
            )
        )
    return {
        "seed": seed,
        "target_steps": steps,
        "steps": stop,
        "resumed_at": start,
        "primitive_successors": primitive_before + carrier.primitive_successors,
        "nonlinear_gate_requests": nonlinear_before + carrier.nonlinear_gate_requests,
        "rows": rows,
        "seconds": elapsed,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=196)
    parser.add_argument("--steps", type=int, default=16)
    parser.add_argument(
        "--chunk",
        type=int,
        help="maximum primitive events in this run; resume the checkpoint for the next chunk",
    )
    parser.add_argument("--resume", type=Path)
    parser.add_argument("--checkpoint", type=Path)
    args = parser.parse_args()
    with exact_oracle():
        report = probe(
            args.seed,
            args.steps,
            chunk=args.chunk,
            resume=args.resume,
            checkpoint=args.checkpoint,
        )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
