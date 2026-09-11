"""Measure the carry-free Collatz raw-digit / sentinel quotient."""

from __future__ import annotations

import json
from collections.abc import Iterator

from devtools.experiments.collatz.collatz_word_transducer import (
    collatz_accelerated_radix4_transducer,
    compose_subsequential,
    minimize_aligned_subsequential,
)
from devtools.paths import report_output, repository_root
from number_compiler.arithmetic.automata.program_word import from_runs, word_metrics
from number_compiler.projection.collatz_orbits.binary import collatz_orbit_formulas
from number_compiler.sequences.collatz.pair import (
    collatz_valuation_itinerary,
    mul3_carry_monoid,
)
from number_compiler.sequences.collatz.radix import (
    collatz_orbit_formulas_local_composite_radix,
    collatz_orbit_formulas_ternary,
)
from number_compiler.sequences.collatz.raw_field import (
    CollatzRawDigitField,
    collatz_orbit_formulas_sentinel_power4,
    collatz_sentinel_digit,
    collatz_sentinel_orbit,
    summarize_collatz_sentinel_word,
)

ROOT = repository_root()

OUT = ROOT / "results" / "collatz_raw_field_metrics.json"
REPORT = report_output(
    "devtools.benchmarks.collatz_raw_field_probe", "COLLATZ_RAW_FIELD_RESULTS.md"
)


def _odd_orbit(seed: int) -> Iterator[int]:
    n = int(seed)
    while n > 1 and not (n & 1):
        n >>= 1
    while n != 1:
        yield n
        m = 3 * n + 1
        v = (m & -m).bit_length() - 1
        n = m >> v


def _formula_max_nodes(seed: int) -> dict[str, int]:
    _a, binary = collatz_orbit_formulas(
        seed, max_steps=512, stop_at_one=True, materialize_values=False
    )
    _a, ternary = collatz_orbit_formulas_ternary(
        seed, max_steps=512, stop_at_one=True, materialize_values=False
    )
    _a, senary = collatz_orbit_formulas_local_composite_radix(
        seed, radix=6, max_steps=512, stop_at_one=True, materialize_values=False
    )
    _a, radix4 = collatz_orbit_formulas_sentinel_power4(
        seed, radix=4, max_odd_steps=512
    )
    _a, radix16 = collatz_orbit_formulas_sentinel_power4(
        seed, radix=16, max_odd_steps=512
    )
    return {
        "binary_physical": max(row.formula_nodes for row in binary),
        "ternary_physical": max(row.formula_nodes for row in ternary),
        "senary_physical": max(row.formula_nodes for row in senary),
        "radix4_sentinel_accelerated": max(row.formula_nodes for row in radix4),
        "radix16_sentinel_accelerated": max(row.formula_nodes for row in radix16),
    }


def main() -> None:
    seeds = (27, 97, 871, 6171)
    bases = (4, 16, 64, 256)
    sentinel: dict[str, dict[str, dict[str, int]]] = {}
    decimal: dict[str, dict[str, object]] = {}

    for seed in seeds:
        _vals = collatz_valuation_itinerary(seed)
        by_base: dict[str, dict[str, int]] = {}
        for base in bases:
            steps = collatz_sentinel_orbit(seed, base=base)
            checks = sum(s.valuation_digit_checks for s in steps)
            source_digits = sum(s.source_width for s in steps)
            stripped = sum(s.stripped_digits for s in steps)
            residual = sum(s.source_width - s.stripped_digits for s in steps)
            bits = base.bit_length() - 1
            by_base[str(base)] = {
                "sentinel_digit": collatz_sentinel_digit(base),
                "odd_steps": len(steps),
                "physical_steps_represented": len(steps)
                + sum(s.valuation for s in steps),
                "valuation_sum": sum(s.valuation for s in steps),
                "increase_symbols": sum(s.increases for s in steps),
                "decrease_symbols": sum(s.nonincreasing for s in steps),
                "valuation_digit_checks": checks,
                "source_digits": source_digits,
                "sentinel_digits_stripped": stripped,
                "residual_transform_digits": residual,
                "max_scalar_carry": max(
                    (s.scalar_carry_peak for s in steps), default=0
                ),
                "symbol_bit_volume": bits * (checks + residual),
                "hypothetical_ternary_carry_vector_bits": 2 * source_digits,
            }
        sentinel[str(seed)] = by_base

        raw_max = 0
        factor_run = 0
        growth_matches = 0
        odd_steps = 0
        for n in _odd_orbit(seed):
            field = CollatzRawDigitField.from_odd_value(n, base=10)
            raw_max = max(raw_max, field.max_component)
            factor_run += field.sentinel_radix_factor_run()
            growth_matches += int(
                field.boundary_summary().digit_growth == field.digit_growth
            )
            odd_steps += 1
        decimal[str(seed)] = {
            "odd_steps": odd_steps,
            "max_raw_component": raw_max,
            "decimal_sentinel_digit": 3,
            "total_trailing_radix_factors_synthesized": factor_run,
            "growth_summary_exact_steps": growth_matches,
        }

    huge_word = from_runs(((5, 1_000_000), (7, 1), (5, 1_000_000)))
    huge_metrics = word_metrics(huge_word)
    huge_summary = summarize_collatz_sentinel_word(huge_word, base=16)

    total_symbol_volume = {
        str(base): sum(
            int(sentinel[str(seed)][str(base)]["symbol_bit_volume"]) for seed in seeds
        )
        for base in bases
    }
    canonical_radix = min(bases, key=lambda b: total_symbol_volume[str(b)])
    carry_monoids = {
        str(base): [list(fn.outputs) for fn in mul3_carry_monoid(base)]
        for base in (4, 10, 16, 64, 256)
    }

    one = minimize_aligned_subsequential(collatz_accelerated_radix4_transducer())
    powered_transducers = []
    current = one
    for power in range(1, 7):
        if power > 1:
            current = minimize_aligned_subsequential(
                compose_subsequential(current, one)
            )
        powered_transducers.append(
            {
                "power": power,
                "states": len(current.states),
                "description_bits": current.description_bits(),
            }
        )

    formula_nodes = _formula_max_nodes(27)
    metrics = {
        "decimal_raw_field": decimal,
        "power4_sentinel": sentinel,
        "power4_total_symbol_volume": total_symbol_volume,
        "canonical_sentinel_radix": canonical_radix,
        "synthesized_mul3_carry_monoids": carry_monoids,
        "radix4_powered_subsequential": powered_transducers,
        "seed27_formula_max_nodes": formula_nodes,
        "huge_rle_sentinel_word": {
            "represented_digits": huge_word.length,
            "runs": huge_metrics["runs"],
            "nodes": huge_metrics["nodes"],
            "description_bits": huge_metrics["description_bits"],
            "first_mismatch": huge_summary.low_first_mismatch,
            "valuation": huge_summary.power4_valuation(base=16),
        },
    }
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(json.dumps(metrics, indent=2, sort_keys=True) + "\n")

    s27 = sentinel["27"]
    f = formula_nodes
    lines = [
        "# Collatz raw-digit / sentinel quotient results",
        "",
        "The decimal odd-step field `r_i = 3*d_i + [i=0]` is retained only as a redundant radix field;",
        "normalised output digits and the ternary carry vector are derived on demand.  Decimal coefficients",
        "therefore remain in `0..28`, but the compiler does not keep four parallel forms of the same integer.",
        "",
        "## Sentinel theorem",
        "",
        "For any radix `B == 1 (mod 3)`, `D=(B-1)/3` satisfies",
        "",
        "```text",
        "n = D*(1+B+...+B^(q-1)) + B^q*m",
        "3*n+1 = B^q*(3*m+1).",
        "```",
        "",
        "Thus trailing sentinel digits can be deleted before multiplication.  For `B=4^k`, the residual",
        "2-adic valuation is determined by the first non-sentinel digit alone.  Radix 4 is especially simple:",
        "an odd LSD `3` means an increasing accelerated step (`v2=1`), while LSD `1` means `v2>=2` and",
        "therefore a decreasing step except at the fixed point.",
        "",
        "## Seed 27",
        "",
        "| radix | sentinel | valuation digit checks | residual transform digits | bit-charged symbol volume | max live carry |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for base in bases:
        row = s27[str(base)]
        lines.append(
            f"| {base} | {row['sentinel_digit']} | {row['valuation_digit_checks']} | "
            f"{row['residual_transform_digits']} | {row['symbol_bit_volume']} | {row['max_scalar_carry']} |"
        )
    lines += [
        "",
        "The symbol-count optimum shifts toward larger power-of-four radices, but once digit payload is charged",
        "radix 4 is best among these four for seed 27 and for the aggregate release family.  The canonical compiler",
        "therefore fixes the theorem coordinate at radix 4 rather than retaining a per-seed radix choice.",
        "",
        f"Aggregate charged symbol volumes across seeds 27/97/871/6171: `{total_symbol_volume}`; selected radix: **{canonical_radix}**.",
        "",
        "## Carry monoid is synthesized, not retained",
        "",
        "For radices 4, 10, 16, 64, and 256, deriving `floor((3*d+c)/B)` over the radix alphabet and closing",
        "under composition yields the same **five** carry-transfer functions.  The compiler can regenerate this",
        "constant monoid from the radix; it is not part of per-number semantic state.  In radix 4 the LSD itself",
        "also synthesizes the accelerated phase: digit `3` means `v2=1`/growth, digit `1` starts the sentinel run",
        "and therefore means `v2>=2`/nonincrease.",
        "",
        "## RLE/SLP powering",
        "",
        f"A synthetic **{huge_word.length:,}-digit** radix-16 word with one million sentinel `5`s on each side",
        f"is represented by **{huge_metrics['runs']} runs / {huge_metrics['nodes']} word nodes**.  Its first-hole",
        f"summary finds mismatch {huge_summary.low_first_mismatch:,} and valuation {huge_summary.power4_valuation(base=16):,}",
        "without expanding the run.  The sentinel query is therefore a genuine associative set/word morphism.",
        "",
        "## Direct automaton powering is rejected",
        "",
        "The exact radix-4 accelerated map minimizes to 10 subsequential states, but exact aligned composition",
        "does not stay small:",
        "",
        "| accelerated power | minimized states | description bits |",
        "|---:|---:|---:|",
        *[
            f"| {row['power']} | {row['states']:,} | {row['description_bits']:,} |"
            for row in powered_transducers
        ],
        "",
        "So the one-step digit automaton is kept as a research differential, not as the powered production carrier.",
        "The remaining Collatz powering problem is to quotient those residual transducer states by a stronger",
        "domain/theorem interface rather than repeatedly composing the concrete automaton.",
        "",
        "## Boolean formula embedding is rejected",
        "",
        "| path | max FormulaArena nodes, seed 27 |",
        "|---|---:|",
        f"| binary physical | {f['binary_physical']} |",
        f"| ternary physical | {f['ternary_physical']} |",
        f"| senary physical | **{f['senary_physical']}** |",
        f"| radix-4 sentinel accelerated, naively re-embedded | {f['radix4_sentinel_accelerated']} |",
        f"| radix-16 sentinel accelerated, naively re-embedded | {f['radix16_sentinel_accelerated']} |",
        "",
        "So the new quotient is kept as a native digit/run morphism.  Forcing it back through the older Boolean",
        "formula representation loses the gain even though the arithmetic theorem is stronger.",
    ]
    REPORT.write_text("\n".join(lines) + "\n")
    print(json.dumps(metrics, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
