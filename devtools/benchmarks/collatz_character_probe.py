"""Deterministic v0.53.6 Collatz lazy-character probe."""

from __future__ import annotations

from devtools.paths import report_directory

import json

from devtools.paths import repository_root
from number_compiler.api.number_api import NumberCompiler
from number_compiler.arithmetic.automata.program_word import from_runs, from_values
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.collatz.character import (
    collatz_growth_character_value,
    collatz_radial_character_word,
    collatz_radial_characters_word,
)

ROOT = repository_root()


def run_probe() -> dict[str, object]:
    growth_checked = growth_mismatches = 0
    phase_checked = phase_mismatches = 0
    orders = (2, 3, 4, 5, 8, 13)
    for n in range(1, 10000, 2):
        k = v2_positive(3 * n + 1)
        growth = collatz_growth_character_value(n)
        growth_checked += 1
        growth_mismatches += int(growth.increases != (k == 1))
        word = from_values(digits_lsd(n, 4))
        chars = collatz_radial_characters_word(word, orders, base=4)
        for order, char in zip(orders, chars, strict=True):
            phase_checked += 1
            phase_mismatches += int(char.shift != k % order)

    q = 10**12 + 123
    huge_word = from_runs(((1, q), (3, 1)))
    huge = collatz_radial_character_word(huge_word, 257, base=4)
    full_k = 2 * q + 1
    api = NumberCompiler()
    api_growth = api.project_collatz_growth(27)
    api_phase = api.project_collatz_radial_character(27, 13)
    return {
        "release": "v0.53.6",
        "growth": {
            "checked": growth_checked,
            "mismatches": growth_mismatches,
            "state_bits": 1,
            "uses_full_valuation": False,
        },
        "radial_phase": {
            "checked": phase_checked,
            "mismatches": phase_mismatches,
            "orders": list(orders),
            "multi_order_strategy": "one-lcm-character-then-quotient",
        },
        "huge_compressed_word": {
            "sentinel_digits": q,
            "exact_valuation_if_materialized": full_k,
            "requested_order": 257,
            "projected_shift": huge.shift,
            "expected_shift": full_k % 257,
            "word_runs": huge_word.run_count,
            "word_length": huge_word.length,
            "character_description_bits": huge.description_bits,
        },
        "number_api": {
            "growth_27_increases": api_growth.increases,
            "phase_27_order13": api_phase.shift,
            "orbit_construction_required": False,
        },
        "scope": {
            "growth_character": "chi4(n)=(-1/n), exact for strict accelerated growth",
            "radial_character": "cyclic/Fourier phase k mod m, not a claim that Jacobi recovers full v2",
            "exact_successor": "full 2-adic germ remains lazy fallback",
        },
    }


def main() -> None:
    result = run_probe()
    out = (
        report_directory("devtools.benchmarks.collatz_character_probe")
        / "collatz_character_metrics.json"
    )
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
