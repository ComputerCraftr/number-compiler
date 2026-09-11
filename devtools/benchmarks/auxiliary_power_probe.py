#!/usr/bin/env python3
"""Measure the small Collatz/prime powered-algebra side experiments."""

from __future__ import annotations

import json

from devtools.paths import repository_root
from number_compiler.sequences.collatz.power import (
    CollatzPowerArena,
    collatz_apply_word,
    collatz_branch_word,
)
from number_compiler.sequences.prime.set import (
    AdditiveTranslation,
    MultiplicativeSetOperator,
    project_odd_prime_block,
)

ROOT = repository_root()


def collatz_metrics() -> dict[str, object]:
    even_powers = []
    oe_powers = []
    for exponent in (1, 4, 16, 64, 256, 1024, 4096):
        arena = CollatzPowerArena()
        root = arena.power(arena.atom("E"), exponent)
        row = {"repetitions": exponent, **arena.metrics(root)}
        even_powers.append(row)

        arena = CollatzPowerArena()
        oe = arena.concat(arena.atom("O"), arena.atom("E"))
        root = arena.power(oe, exponent)
        row = {"repetitions": exponent, **arena.metrics(root)}
        oe_powers.append(row)

    seed27 = []
    word = collatz_branch_word(27, 111)
    for steps in (8, 16, 32, 64, 96, 111):
        arena = CollatzPowerArena()
        root = arena.from_branches(word[:steps])
        assert root.effect.apply(27) == collatz_apply_word(27, word[:steps])
        seed27.append({"steps": steps, **arena.metrics(root)})

    return {
        "even_branch_power": even_powers,
        "odd_even_macro_power": oe_powers,
        "seed_27_path": seed27,
    }


def prime_metrics() -> dict[str, object]:
    p = 9_999_991
    lanes = []
    for length in (16, 64, 256, 1024, 4096):
        projection = project_odd_prime_block(p + 2, length)
        lanes.append(
            {
                "candidates": length,
                "natural_factor_lanes": projection.natural_lanes,
                "canonical_lanes": len(projection.canonical_lanes),
                "prime_count": projection.summary.count,
                "first_prime_index": projection.summary.first,
            }
        )

    projection = project_odd_prime_block(p + 2, 64)
    first_index = projection.summary.first
    assert first_index is not None
    first_prime = p + 2 + 2 * first_index
    assert first_prime == 10_000_019

    left = project_odd_prime_block(p + 2, 256).summary
    right = project_odd_prime_block(p + 2 + 2 * 256, 256).summary
    whole = project_odd_prime_block(p + 2, 512).summary
    assert left.then(right) == whole

    symbolic = AdditiveTranslation.power_of_two(1_000_000)
    translated = MultiplicativeSetOperator.at(p).translate(symbolic)
    doubled = symbolic.then(symbolic)

    return {
        "lane_projection": lanes,
        "first_prime": first_prime,
        "summary_halves": {
            "left": {"length": left.length, "count": left.count, "first": left.first},
            "right": {
                "length": right.length,
                "count": right.count,
                "first": right.first,
            },
            "composed": {
                "length": whole.length,
                "count": whole.count,
                "first": whole.first,
            },
        },
        "symbolic_translation": {
            "operator_nodes": translated.operator_nodes,
            "description_bits": translated.description_bits,
            "pow2_exponent": 1_000_000,
            "double_normalizes_to_exponent": doubled.pow2_exponents[0],
        },
    }


def main() -> None:
    data = {"collatz": collatz_metrics(), "prime": prime_metrics()}
    out = ROOT / "results" / "auxiliary_power_metrics.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(json.dumps(data, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
