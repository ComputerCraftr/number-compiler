"""Cross-family compilation with explicitly scoped reverse carry-history proofs."""

from __future__ import annotations

import json
from typing import NotRequired, TypedDict, cast

from devtools.benchmarks.json_support import jsonable
from devtools.paths import report_directory, report_output, repository_root
from devtools.verification import exact_oracle
from devtools.verification.sequence_diagnostics import with_carry_diagnostics
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import (
    CollatzSequenceSpec,
    FermatSequenceSpec,
    MersenneSequenceSpec,
    PrimeBlockSequenceSpec,
    ReverseAddSequenceSpec,
)
from number_compiler.sequences.prime.coordinates import (
    prime_block_summary_hyperbolic_packed,
)
from number_compiler.sequences.prime.quotient import prime_block_summary_quotient


class WorkerReport(TypedDict):
    rows: list[dict[str, object]]
    cache_entries: int
    raw_rows: NotRequired[list[dict[str, object]]]


ROOT = repository_root()


@exact_oracle()
def _reverse_worker() -> WorkerReport:
    compiler = CanonicalSequenceCompiler()
    seeds = (1, 89, 195, 196, 197, 4994)
    bases = (2, 3, 4, 5, 7, 8, 10, 12, 16)
    rows: list[dict[str, object]] = []
    for base in bases:
        for seed in seeds:
            result = compiler.compile_diagnostic(ReverseAddSequenceSpec(seed, base, 24))
            if base >= 3:
                result = with_carry_diagnostics(result)
            rows.append(
                {
                    "seed": seed,
                    "base": base,
                    "steps": result.spec.steps,
                    "final_width": result.terms[-1].width,
                    "final_formula_nodes": result.terms[-1].formula_nodes,
                    "final_formula_description_bits": result.terms[
                        -1
                    ].formula_description_bits,
                    "live_rows_average": result.live_rows_average,
                    "live_rows_max": result.live_rows_max,
                    "live_carry_bits_ratio": result.live_carry_bits_ratio,
                    "cyclotomic_memory_max": dict(result.cyclotomic_memory_max),
                    "growth_state_classes": result.growth_state_classes,
                    "growth_state_max_bits": result.growth_state_max_bits,
                    "carry_reset_max_bits": result.carry_reset_max_bits,
                }
            )
    return {"rows": rows, "cache_entries": compiler.cache_size}


def _collatz_worker() -> WorkerReport:
    rows: list[dict[str, object]] = []
    raw_rows: list[dict[str, object]] = []
    cache_entries = 0
    for seed in (97, 27, 7, 3, 1):
        compiler = CanonicalSequenceCompiler()
        raw = None
        for radix in (2, 3):
            result = compiler.compile_diagnostic(CollatzSequenceSpec(seed, radix, 128))
            widths: list[int] = []
            for term in result.terms:
                assert isinstance(term.width, int)
                widths.append(term.width)
            rows.append(
                {
                    "seed": seed,
                    "radix": radix,
                    "physical_terms": len(result.terms),
                    "valuation_symbols": (
                        0
                        if result.raw_field_quotient is None
                        else result.raw_field_quotient.odd_steps
                    ),
                    "max_width": max(widths, default=0),
                    "max_formula_nodes": max(
                        (t.formula_nodes for t in result.terms), default=0
                    ),
                    "final_value": result.terms[-1].value if result.terms else None,
                    "valuation_state_classes": result.valuation_state_classes,
                    "valuation_state_max_bits": result.valuation_state_max_bits,
                }
            )
            raw = result.raw_field_quotient
        if raw is None:
            raise AssertionError(seed)
        raw_rows.append(
            {
                "seed": seed,
                "radix": raw.radix,
                "sentinel_digit": raw.sentinel_digit,
                "odd_steps": raw.odd_steps,
                "valuation_sum": raw.valuation_sum,
                "increase_symbols": raw.increase_symbols,
                "nonincreasing_symbols": raw.nonincreasing_symbols,
                "valuation_digit_checks": raw.valuation_digit_checks,
                "source_digits": raw.source_digits,
                "stripped_digits": raw.stripped_digits,
                "residual_transform_digits": raw.residual_transform_digits,
                "scalar_carry_peak": raw.scalar_carry_peak,
            }
        )
        cache_entries += compiler.cache_size
    return {"rows": rows, "raw_rows": raw_rows, "cache_entries": cache_entries}


def _prime_worker() -> WorkerReport:
    compiler = CanonicalSequenceCompiler()
    rows: list[dict[str, object]] = []
    for length in (64, 256, 1024, 4096):
        compiled = compiler.compile_diagnostic(
            PrimeBlockSequenceSpec(9_999_993, length)
        )
        decision = compiled.decision
        packed = prime_block_summary_hyperbolic_packed(9_999_993, length)
        quotient = prime_block_summary_quotient(9_999_993, length)
        if decision.summary != packed.summary or decision.summary != quotient.summary:
            raise AssertionError("prime projector differential mismatch")
        rows.append(
            {
                "length": length,
                "prime_count": decision.summary.count,
                "first": decision.summary.first,
                "lane_quotient_interfaces": decision.semantic_interfaces,
                "lane_quotient_nodes": decision.decision_nodes,
                "lane_quotient_description_bits": decision.decision_description_bits,
                "lane_transform_checks": decision.lane_transform_checks,
                "lane_transform_cache_hits": decision.transform_cache_hits,
                "lane_radix_projection_work": decision.radix_projection_work,
                "lane_projection_work": decision.projection_work,
                "factor_generator_gcd_calls": decision.factor_generator_gcd_calls,
                "packed_cofactor_points": packed.cofactor_points,
                "packed_roughness_word_gcds": packed.roughness_word_gcds,
                "packed_first_hole_word_gcds": packed.first_hole_word_gcds,
                "packed_groups": packed.packed_groups,
                "quotient_pi_queries": quotient.pi_queries,
                "quotient_max_states": quotient.max_quotient_states,
                "quotient_sieve_updates": quotient.total_sieve_updates,
            }
        )
    return {"rows": rows, "cache_entries": compiler.cache_size}


def _run_worker(name: str) -> WorkerReport:
    import os
    import subprocess
    import sys

    output = subprocess.check_output(
        [
            sys.executable,
            "-m",
            "devtools.benchmarks.sequence_family_probe",
            "--worker",
            name,
        ],
        env=os.environ.copy(),
        text=True,
    )
    decoded: object = json.loads(output)
    if (
        not isinstance(decoded, dict)
        or not isinstance(decoded.get("rows"), list)
        or type(decoded.get("cache_entries")) is not int
    ):
        raise ValueError("invalid sequence worker report")
    return cast("WorkerReport", decoded)


def _number(row: dict[str, object], field: str) -> int | float:
    value = row[field]
    if type(value) not in (int, float):
        raise ValueError(f"non-numeric report field: {field}")
    return cast(int | float, value)


def main() -> None:
    # Reverse-add and Collatz can retain large independent formula arenas.
    # Compile them in isolated workers so arena-local identities never share a
    # process lifetime merely for benchmark aggregation.
    reverse_data = _run_worker("reverse")
    collatz_data = _run_worker("collatz")
    reverse_rows = list(reverse_data["rows"])
    collatz_rows = list(collatz_data["rows"])
    collatz_raw_rows = list(collatz_data["raw_rows"])
    reverse_cache_entries = int(reverse_data["cache_entries"])
    collatz_cache_entries = int(collatz_data["cache_entries"])
    seeds = (1, 89, 195, 196, 197, 4994)
    bases = (2, 3, 4, 5, 7, 8, 10, 12, 16)

    special_compiler = CanonicalSequenceCompiler()
    fermat = special_compiler.compile_diagnostic(
        FermatSequenceSpec((0, 1, 2, 3, 4, 5, 6, 8, 12), 5)
    )
    fermat_rows = [
        {
            "index": t.index,
            "number_bits": t.number_bits,
            "cyclotomic_order": t.cyclotomic_order,
            "radix_runs": t.radix_word.runs,
            "radix_word_nodes": t.radix_word.word_nodes,
            "radix_description_bits": t.radix_word.word_description_bits,
            "projection_method": t.projection_method,
            "factor_witness": t.factor_witness,
            "pepin_squarings": None
            if t.primality is None
            else t.primality.specialization_raw_squarings,
            "pepin_passes": None if t.primality is None else t.primality.passes,
        }
        for t in fermat.terms
    ]

    mersenne = special_compiler.compile_diagnostic(
        MersenneSequenceSpec((2, 3, 5, 7, 11, 13, 15, 17, 19, 23, 31, 127, 8191), 31)
    )
    mersenne_rows = [
        {
            "exponent": t.exponent,
            "number_bits": t.number_bits,
            "radix_runs": t.radix_word.runs,
            "radix_word_nodes": t.radix_word.word_nodes,
            "radix_description_bits": t.radix_word.word_description_bits,
            "composite_exponent_factor": (
                None
                if t.composite_exponent_factor is None
                else t.composite_exponent_factor.exponent
            ),
            "projection_method": t.projection_method,
            "factor_witness": t.factor_witness,
            "lucas_lehmer_iterations": None
            if t.primality is None
            else t.primality.specialization_raw_squarings,
            "lucas_lehmer_passes": None if t.primality is None else t.primality.passes,
        }
        for t in mersenne.terms
    ]

    prime_data = _run_worker("prime")
    prime_rows = list(prime_data["rows"])
    prime_cache_entries = int(prime_data["cache_entries"])

    data = {
        "reverse_add": reverse_rows,
        "collatz": collatz_rows,
        "collatz_raw_field": collatz_raw_rows,
        "fermat": fermat_rows,
        "mersenne": mersenne_rows,
        "prime": prime_rows,
        "compiler_cache_entries": {
            "reverse_add": reverse_cache_entries,
            "collatz": collatz_cache_entries,
            "special": special_compiler.cache_size,
            "prime": prime_cache_entries,
        },
    }
    out_json = (
        report_directory("devtools.benchmarks.sequence_family_probe")
        / "sequence_family_metrics.json"
    )
    out_json.write_text(
        json.dumps(jsonable(data), sort_keys=True, separators=(",", ":")) + "\n"
    )

    live = [r for r in reverse_rows if r["live_rows_average"] is not None]
    md = [
        "# Cross-family canonical sequence compiler results",
        "",
        "The suite uses the production `CanonicalSequenceCompiler`; benchmark/test helpers are not imported by it.",
        "",
        "## Reverse-and-add seed/base matrix",
        "",
        f"Compiled {len(reverse_rows)} exact 24-step orbits: seeds {list(seeds)}, bases {list(bases)}.",
        f"Live carry suffix average range: {min(_number(r, 'live_rows_average') for r in live):.3f}..{max(_number(r, 'live_rows_average') for r in live):.3f} rows.",
        f"Live carry suffix maximum across the matrix: {max(_number(r, 'live_rows_max') for r in live)} rows.",
        f"Charged live/fixed-H carry-bit ratio range: {min(_number(r, 'live_carry_bits_ratio') for r in live):.4f}..{max(_number(r, 'live_carry_bits_ratio') for r in live):.4f}.",
        f"Exact current-growth observer class range: {min(_number(r, 'growth_state_classes') for r in reverse_rows)}..{max(_number(r, 'growth_state_classes') for r in reverse_rows)} classes; maximum charged observer size {max(_number(r, 'growth_state_max_bits') for r in reverse_rows)} bits versus reset-signature {max(_number(r, 'carry_reset_max_bits') for r in reverse_rows)} bits.",
        "",
        "## Collatz raw-field theorem interface",
        "",
        "Every Collatz compilation now carries one fixed radix-4 sentinel theorem summary as derived metadata.",
        "It synthesizes accelerated valuation and growth/nonincrease phase from the digit word and charges only",
        "first-hole checks plus residual target-digit work; source/raw/normalized/carry vectors are not retained.",
        f"The retained accelerated projection sees at most {max(_number(r, 'valuation_state_classes') for r in collatz_rows)} distinct valuation-action states in this suite, with maximum charged state size {max(_number(r, 'valuation_state_max_bits') for r in collatz_rows)} bits; the explicit valuation symbol itinerary is an on-demand view only.",
        "",
        "| seed | odd symbols | valuation sum | digit checks | stripped digits | residual digits | scalar carry peak |",
        "|---:|---:|---:|---:|---:|---:|---:|",
        *[
            f"| {r['seed']} | {r['odd_steps']} | {r['valuation_sum']} | {r['valuation_digit_checks']} | {r['stripped_digits']} | {r['residual_transform_digits']} | {r['scalar_carry_peak']} |"
            for r in collatz_raw_rows
        ],
        "",
        "## Special binary families",
        "",
        "Fermat radix programs have at most three runs; Mersenne radix programs have one run.  Their retained radix descriptions therefore grow logarithmically in represented bit length.  The factored digit observer now short-circuits a long primality projection when it already proves a proper factor; otherwise Pepin/Lucas-Lehmer iteration counts remain separately charged.",
        "After a prime projection succeeds in the bounded theorem range, the modular residue is replaced by the exact closed order-depth Moore state; failed/composite projections do not receive that prime-group state.",
        "",
        "| family term | represented bits | radix runs | radix description bits | primality iterations |",
        "|---|---:|---:|---:|---:|",
    ]
    for t in fermat.terms:
        if t.index in (5, 8, 12):
            md.append(
                f"| F_{t.index} | {t.number_bits} | {t.radix_word.runs} | {t.radix_word.word_description_bits} | "
                f"{('factor ' + str(t.factor_witness) if t.factor_witness is not None else ('—' if t.primality is None else t.primality.specialization_raw_squarings))} |"
            )
    for mersenne_term in mersenne.terms:
        if mersenne_term.exponent in (31, 127, 8191):
            md.append(
                f"| M_{mersenne_term.exponent} | {mersenne_term.number_bits} | {mersenne_term.radix_word.runs} | {mersenne_term.radix_word.word_description_bits} | "
                f"{('factor ' + str(mersenne_term.factor_witness) if mersenne_term.factor_witness is not None else ('—' if mersenne_term.primality is None else mersenne_term.primality.specialization_raw_squarings))} |"
            )
    md += [
        "",
        "## Prime block projection",
        "",
        "The production block projector is now the residual-divisor set morphism.  The packed-hyperbolic and floor-quotient implementations are independent benchmark/differential paths rather than duplicate retained compiler state.",
        "",
        "| candidates | residual interfaces | arithmetic transforms | cached transforms | radix work | packed cofactor points | quotient states | quotient updates |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in prime_rows:
        md.append(
            f"| {row['length']} | {row['lane_quotient_interfaces']} | {row['lane_transform_checks']} | {row['lane_transform_cache_hits']} | {row['lane_radix_projection_work']} | {row['packed_cofactor_points']} | {row['quotient_max_states']} | {row['quotient_sieve_updates']} |"
        )
    md += [
        "",
        "## Bound status",
        "",
        "* Fermat/Mersenne **radix generation/projection** is sublinear in represented digit length because the exact binary words are canonical RLE programs.",
        "* Fermat Pepin and Mersenne Lucas-Lehmer **primality projection** remains linear in represented bit length/iteration count in this implementation.",
        "* Prime floor-quotient summary is sublinear in block length for fixed magnitude, but remains O(sqrt(n)) in magnitude.",
        "* The retained prime residual-divisor projector reuses exact single-lane radix morphisms before interface construction.  Transform work is sublinear-looking in the measured block window, while retained decision description remains roughly linear; this is not a universal sublinear theorem.",
        "* Reverse-add current growth no longer retains a linear growth itinerary: it is emitted from the logarithmic boundary valuation/sign observer already present in the canonical summary.  That observer is not successor-closed, so the full-J blocker remains the reduced-state successor, not current growth extraction.",
        "* Collatz no longer retains the linear valuation-symbol itinerary beside the composed valuation slab.  A single `k=v2(3n+1)` is the exact accelerated action and cyclotomic shift phase, but `k_t` is not a closed orbit state.",
        "* Fermat/Mersenne successful prime projections can discard the modular residue in favor of a logarithmic-size closed order-depth state; its one-time extraction is still charged and is not claimed asymptotically cheaper than the original recurrence.",
    ]
    (
        report_output(
            "devtools.benchmarks.sequence_family_probe", "SEQUENCE_FAMILY_RESULTS.md"
        )
    ).write_text("\n".join(md) + "\n")
    print(out_json)
    print(
        report_output(
            "devtools.benchmarks.sequence_family_probe", "SEQUENCE_FAMILY_RESULTS.md"
        )
    )


def _command() -> None:
    import sys

    if len(sys.argv) == 3 and sys.argv[1] == "--worker":
        if sys.argv[2] == "reverse":
            print(json.dumps(_reverse_worker(), sort_keys=True))
        elif sys.argv[2] == "collatz":
            print(json.dumps(_collatz_worker(), sort_keys=True))
        elif sys.argv[2] == "prime":
            print(json.dumps(_prime_worker(), sort_keys=True))
        else:
            raise SystemExit(f"unknown worker: {sys.argv[2]}")
    else:
        main()


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(_command))
