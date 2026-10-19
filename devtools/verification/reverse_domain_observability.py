"""Finite exact diagnostic; never a runtime quotient or unbounded proof."""

from __future__ import annotations

import argparse
import json
from itertools import product

from devtools.verification import exact_oracle, require_exact_oracle
from number_compiler.arithmetic.carry.carry_itinerary import carry_threshold_itinerary
from number_compiler.arithmetic.carry.event_memory import pair_step


def domain_observability(width: int, horizon: int) -> dict[str, object]:
    """Refine by complete domain observations through a bounded horizon.

    Labels intern exact observation histories, with no probabilistic hashing.
    Only the current exact field is retained for each test source. This is an
    oracle diagnostic; these labels are forbidden as production future IDs.
    """
    require_exact_oracle()
    if type(width) is not int or not 1 <= width <= 8:
        raise ValueError("diagnostic width must be one to eight")
    if type(horizon) is not int or not 0 <= horizon <= 20:
        raise ValueError("diagnostic horizon must be zero to twenty")
    axes = [range(19)] * (width // 2)
    if width % 2:
        axes.append(range(0, 19, 2))
    fields = [
        half + (half[:-1] if width % 2 else half)[::-1] for half in product(*axes)
    ]
    source_count = len(fields)
    labels = [0] * source_count
    counts: list[tuple[int, int]] = []
    for step in range(horizon + 1):
        classes: dict[tuple[int, tuple[int, ...]], int] = {}
        next_labels: list[int] = []
        for previous, field in zip(labels, fields, strict=True):
            key = previous, carry_threshold_itinerary(field)
            next_labels.append(classes.setdefault(key, len(classes)))
        labels = next_labels
        counts.append((step, len(classes)))
        if len(classes) == source_count or step == horizon:
            break
        fields = [pair_step(field, 10)[0] for field in fields]
    return {
        "width": width,
        "sources": source_count,
        "domain_history_classes_by_horizon": counts,
        "injective_horizon": counts[-1][0] if counts[-1][1] == source_count else None,
        "unbounded_proof": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-width", type=int, default=6, choices=range(1, 9))
    parser.add_argument("--horizon", type=int, default=20, choices=range(21))
    args = parser.parse_args()
    with exact_oracle():
        reports = [
            domain_observability(width, args.horizon)
            for width in range(1, args.max_width + 1)
        ]
    print(
        json.dumps(
            {"scope": "finite symmetric pair fields", "reports": reports}, indent=2
        )
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
