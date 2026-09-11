"""Reachable decimal endpoint partitions and charged dyadic publication audit."""

from __future__ import annotations

import argparse
from collections.abc import Iterator
import json

from devtools.proofs.endpoint_seam_audit import (
    BoundedEndpointPowerArena,
    audit_endpoint_frontier,
)
from devtools.proofs.reverse_successor_image_audit import _sources
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.radix import reverse_pair_sums

Pair = tuple[int, ...]


def decimal_step(source: Pair) -> Pair:
    return pair_step(source, 10)[0]


def reachable_pairs(width: int) -> Iterator[Pair]:
    """Pair sums of positive width-digit words; center is even, outer sum nonzero."""
    if type(width) is not int or not 2 <= width <= 8:
        raise ValueError("bounded reachable pair width must be in 2..8")
    yield from _sources(width, leading_nonzero=True)


def neighborhood_sources() -> set[Pair]:
    sources: set[Pair] = set()
    for seed in range(176, 217):
        pair = reverse_pair_sums(seed, 10)
        for _ in range(96):
            sources.add(pair)
            pair = decimal_step(pair)
    return sources


def orbit_sources(steps: int = 4095) -> Iterator[Pair]:
    if not 1 <= steps <= 4095:
        raise ValueError("bounded orbit horizon exceeded")
    pair = reverse_pair_sums(196, 10)
    for _ in range(steps):
        yield pair
        pair = decimal_step(pair)


def power_growth() -> list[dict[str, int]]:
    arena = BoundedEndpointPowerArena(decimal_step, max_entries=4096)
    source = reverse_pair_sums(196, 10)
    rows = []
    for level in range(4, 11):
        target = arena.power(source, level)
        cold = arena.primitive_successors
        assert arena.power(source, level) == target
        rows.append(
            {
                "duration": 1 << level,
                "endpoint_width": len(target),
                "primitive_successors": cold,
                "warm_primitive_delta": arena.primitive_successors - cold,
                "retained_results": arena.retained_results,
                "retained_endpoints": arena.retained_endpoints,
                "result_memo_hits": arena.memo_hits,
                "endpoint_publication_hits": arena.endpoint_intern_hits,
                "dyadic_compositions": arena.compositions,
            }
        )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--corpus",
        choices=("widths", "width8", "neighborhood", "orbit", "power"),
        default="width8",
    )
    args = parser.parse_args()
    if args.corpus == "widths":
        result: object = [
            {
                "width": width,
                **audit_endpoint_frontier(
                    reachable_pairs(width),
                    decimal_step,
                    horizons=(1,),
                    spatial_size=len,
                ),
            }
            for width in range(4, 9)
        ]
    elif args.corpus == "power":
        result = {
            "seed": 196,
            "rows": power_growth(),
            "first_use_sublinear_certified": False,
        }
    else:
        sources = (
            reachable_pairs(8)
            if args.corpus == "width8"
            else iter(neighborhood_sources())
            if args.corpus == "neighborhood"
            else orbit_sources()
        )
        result = audit_endpoint_frontier(
            sources,
            decimal_step,
            horizons=(1,) if args.corpus == "orbit" else (1, 2, 4, 8, 16, 32),
            spatial_size=len,
        )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
