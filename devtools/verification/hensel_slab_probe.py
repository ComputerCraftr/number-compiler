"""Measure source-free forcing-slab squaring, separately from occurrence orbits."""

from __future__ import annotations

import argparse
import json
from time import perf_counter
from unittest.mock import patch

from devtools.verification import exact_oracle
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.collatz.frame import CollatzAffineSuffixGerm
from number_compiler.sequences.collatz.hensel_cylinders import (
    HenselAffineBlock,
    HenselCylinder,
)
from number_compiler.sequences.collatz.hensel_slabs import HenselSlabArena


def probe(mode: str, levels: int) -> dict[str, object]:
    if type(levels) is not int or not 0 <= levels <= 10:
        raise ValueError("probe levels must lie in 0..10")
    started = perf_counter()
    arena = HenselSlabArena(max_precision=2048, max_work=1000000)
    if mode == "collatz-branch":
        action = arena.primitive(1, arena.intern(((1, HenselCylinder(6, -1)),)))
    elif mode == "unit-clock":
        action = arena.primitive_block(
            HenselAffineBlock(1, 0, 0),
            HenselCylinder(0, 0),
            arena.intern(((1, HenselCylinder(6, 1)),)),
        )
    elif mode == "halving-stress":
        action = arena.primitive_block(
            HenselAffineBlock(0, 1, 0),
            HenselCylinder(1, 0),
            arena.intern(((1, HenselCylinder(1, 1)),)),
        )
    else:
        raise ValueError("unknown slab probe")
    rows: list[dict[str, object]] = []
    stage = 1
    try:
        for level in range(levels + 1):
            count = 1 << level
            row: dict[str, object] = {
                "events": count,
                **arena.metrics(action.slab),
                "admissible_precision": action.domain.bits if action.domain else None,
                "transport_offset_bits": action.transport.offset.bit_length(),
                "primitive_constructions": arena.primitive_constructions,
                "temporal_compositions": arena.temporal_compositions,
                "seconds": perf_counter() - started,
            }
            rows.append(row)
            print(json.dumps({"checkpoint": row}), flush=True)
            # Independent indexed controls, outside the composition poison.
            if mode == "collatz-branch":
                assert action.domain == HenselCylinder(count + 1, -1)
                source_bits = max(count + 1, 6)
                source = (1 << source_bits) - 1
                assert (
                    action.transport.apply_exact(source)
                    == (3**count << (source_bits - count)) - 1
                )
                assert arena.evaluate(action.slab, source) == frozenset((1,))
            elif mode == "unit-clock":
                expected = {pow(3, -j, 64) for j in range(count)}
                for value in range(64):
                    assert bool(arena.evaluate(action.slab, value)) == (
                        value in expected
                    )
            else:
                # A dyadic halving slab is an algebra stress test, not an
                # accelerated odd Collatz itinerary. Its union is v2(x)<N.
                assert arena.evaluate(action.slab, 1 << (count - 1)) == frozenset((1,))
                assert not arena.evaluate(action.slab, 1 << count)
                assert arena.metrics(action.slab)["atoms"] == count
            if level == levels:
                break
            stage = 2 * count
            failure = AssertionError(
                "primitive or concrete midpoint used while squaring"
            )
            with (
                patch.object(arena, "primitive", side_effect=failure),
                patch.object(arena, "primitive_block", side_effect=failure),
                patch.object(arena, "evaluate", side_effect=failure),
                patch.object(HenselAffineBlock, "apply_exact", side_effect=failure),
                patch.object(CollatzAffineSuffixGerm, "next_step", side_effect=failure),
            ):
                action = arena.compose(action, action)
            assert arena.primitive_constructions == 1
        return {"status": "complete", "mode": mode, "rows": rows}
    except BlockContextBudgetExceeded as error:
        return {
            "status": "budget_exceeded",
            "mode": mode,
            "stage": stage,
            "error": str(error),
            "rows": rows,
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mode",
        choices=("collatz-branch", "unit-clock", "halving-stress"),
        default="collatz-branch",
    )
    parser.add_argument("--levels", type=int, default=10)
    args = parser.parse_args()
    with exact_oracle():
        result = probe(args.mode, args.levels)
    print(json.dumps(result, indent=2), flush=True)


if __name__ == "__main__":
    main()
