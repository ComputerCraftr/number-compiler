"""Measure exact projection observers and their extraction barriers."""

from __future__ import annotations

from devtools.paths import report_directory

import json

from devtools.experiments.algebra.projection_observer import (
    collatz_parity_observer_profile,
    fermat_squaring_observer_profile,
    mersenne_lucas_observer_profile,
    prime_lane_observer_profile,
    prime_wheel_observer_profile,
    reverse_add_admissible_growth_words,
    reverse_add_growth_observer_profile,
)
from devtools.paths import report_output, repository_root
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import FermatSequenceSpec, MersenneSequenceSpec
from number_compiler.arithmetic.fields.radix import digits_lsd

ROOT = repository_root()


def _reverse_value(value: int, base: int) -> int:
    ds = digits_lsd(value, base)
    out = 0
    for digit in ds:
        out = out * base + digit
    return out


def _reverse_growths(seed: int, base: int, steps: int) -> tuple[int, ...]:
    value = int(seed)
    out = []
    for _ in range(int(steps)):
        width = len(digits_lsd(value, base))
        nxt = value + _reverse_value(value, base)
        out.append(len(digits_lsd(nxt, base)) - width)
        value = nxt
    return tuple(out)


def _trace_counts(bits: tuple[int, ...], horizons: tuple[int, ...]) -> dict[str, int]:
    return {
        str(h): len({tuple(bits[i : i + h]) for i in range(len(bits) - h + 1)})
        for h in horizons
        if h <= len(bits)
    }


def main() -> None:
    reverse = reverse_add_growth_observer_profile()
    growth_language = [
        reverse_add_admissible_growth_words(h) for h in (4, 8, 16, 32, 64)
    ]
    trace = _reverse_growths(196, 10, 1024)

    collatz = [collatz_parity_observer_profile(k) for k in (4, 8, 12, 16)]
    lanes = [prime_lane_observer_profile(q) for q in (3, 5, 7, 11, 31)]
    wheels = [
        prime_wheel_observer_profile(fs) for fs in ((3, 5), (3, 5, 7), (3, 5, 7, 11))
    ]
    fermat = [fermat_squaring_observer_profile(n) for n in range(5)]
    mersenne = [mersenne_lucas_observer_profile(p) for p in (3, 5, 7, 11, 13)]

    compiler = CanonicalSequenceCompiler()
    f5 = compiler.compile_diagnostic(FermatSequenceSpec((5,), test_through=5)).terms[0]
    m11, m23, m31 = compiler.compile_diagnostic(
        MersenneSequenceSpec((11, 23, 31), test_through=31)
    ).terms

    data = {
        "reverse_add": {
            "scan_states": reverse.scan_states,
            "block_transformations": reverse.block_transformations,
            "transformation_bits": reverse.transformation_bits,
            "universal_growth_language": [
                {
                    "horizon": p.horizon,
                    "words": p.exact_projection_words,
                    "required_bits": p.required_bits,
                    "bits_per_step": p.required_bits / p.horizon if p.horizon else 0.0,
                }
                for p in growth_language
            ],
            "seed196_distinct_growth_traces": _trace_counts(
                trace, (1, 2, 4, 8, 12, 16, 24, 32)
            ),
        },
        "collatz": [
            {
                "horizon": p.horizon,
                "projection_words": p.exact_projection_words,
                "required_bits": p.required_bits,
            }
            for p in collatz
        ],
        "prime_lanes": [
            p.__dict__
            if hasattr(p, "__dict__")
            else {
                "name": p.name,
                "source_states": p.source_states,
                "observer_classes": p.observer_classes,
                "source_bits": p.source_bits,
                "observer_bits": p.observer_bits,
                "refinement_rounds": p.refinement_rounds,
            }
            for p in lanes
        ],
        "prime_wheels": [
            {
                "name": p.name,
                "source_states": p.source_states,
                "observer_classes": p.observer_classes,
                "source_bits": p.source_bits,
                "observer_bits": p.observer_bits,
                "refinement_rounds": p.refinement_rounds,
            }
            for p in wheels
        ],
        "fermat": [
            {
                "index": n,
                "modulus": p.source_states,
                "observer_classes": p.observer_classes,
                "source_bits": p.source_bits,
                "observer_bits": p.observer_bits,
                "refinement_rounds": p.refinement_rounds,
                "generic_pepin_squarings": (1 << n) - 1,
            }
            for n, p in enumerate(fermat)
        ],
        "mersenne": [
            {
                "exponent": e,
                "modulus": p.source_states,
                "observer_classes": p.observer_classes,
                "source_bits": p.source_bits,
                "observer_bits": p.observer_bits,
                "refinement_rounds": p.refinement_rounds,
                "initial_class": p.initial_class,
                "generic_ll_iterations": e - 2,
            }
            for e, p in zip((3, 5, 7, 11, 13), mersenne)
        ],
        "digit_observer_short_circuit": {
            "F5": {
                "method": f5.projection_method,
                "factor": f5.factor_witness,
                "pepin_squarings_avoided": 31,
                "pepin_materialized": f5.primality is not None,
                "digit_square_projection_materialized": f5.digit_projection is not None,
            },
            "M11": {
                "method": m11.projection_method,
                "factor": m11.factor_witness,
                "ll_iterations_avoided": 9,
                "ll_materialized": m11.primality is not None,
                "digit_square_projection_materialized": m11.digit_projection
                is not None,
            },
            "M23": {
                "method": m23.projection_method,
                "factor": m23.factor_witness,
                "ll_iterations_avoided": 21,
                "ll_materialized": m23.primality is not None,
                "digit_square_projection_materialized": m23.digit_projection
                is not None,
            },
            "M31": {
                "method": m31.projection_method,
                "factor": m31.factor_witness,
                "ll_iterations": 29,
                "passes": bool(m31.primality and m31.primality.passes),
            },
        },
    }
    outdir = report_directory("devtools.benchmarks.projection_observer_probe")
    outdir.mkdir(exist_ok=True)
    (outdir / "projection_observer_metrics.json").write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n"
    )

    lines = [
        "# Projection observer quotient results",
        "",
        "Two states merge only after exact Moore/Myhill--Nerode refinement of the projection process.",
        "Short bounded traces are reported separately and never authorize a production merge.",
        "",
        "## Reverse-and-add",
        "",
        "The per-digit carry/growth observer is already the 3-element transformation monoid `CONST0 / ID / CONST1` on two carry states.",
        "The universal no-four-consecutive-growth theorem reduces the future growth language, but not to a finite temporal quotient:",
        "",
        "| horizon | admissible growth words | information bits | bits/step |",
        "|---:|---:|---:|---:|",
    ]
    for p in growth_language:
        lines.append(
            f"| {p.horizon} | {p.exact_projection_words:,} | {p.required_bits} | {p.required_bits / p.horizon:.4f} |"
        )
    lines += [
        "",
        "The asymptotic information rate therefore remains linear in temporal horizon even though one *current* growth projection is constant-state.",
        "",
        "## Collatz",
        "",
        "The finite parity coordinate `Q_k` is bijective modulo `2^k`.  Exact future parity observers therefore have no nontrivial universal quotient:",
        "",
        "| horizon k | exact future words | required bits |",
        "|---:|---:|---:|",
    ]
    for p in collatz:
        lines.append(
            f"| {p.horizon} | {p.exact_projection_words:,} | {p.required_bits} |"
        )
    lines += [
        "",
        "This is an information lower bound, not a weakness of the radix-4 sentinel implementation: the sentinel quotient makes each *next* valuation/phase projection cheap, but arbitrary future parity data still carries one independent bit per normalized step.",
        "",
        "## Prime congruence observers",
        "",
        "A single odd divisor lane has exactly `q` Moore classes under candidate translation by `+2`; the residue coordinate is already minimal.  Raw wheel products are also unminimized:",
        "",
        "| observer | source states | minimal classes |",
        "|---|---:|---:|",
    ]
    for prime_observer in lanes + wheels:
        lines.append(
            f"| `{prime_observer.name}` | {prime_observer.source_states:,} | {prime_observer.observer_classes:,} |"
        )
    lines += [
        "",
        "Hence CRT/factored congruence is not optional bookkeeping: it is the compact representation of an otherwise product-sized exact observer.  The residual-divisor interval morphism remains the path that avoids expanding that universal wheel for block summaries.",
        "",
        "## Fermat squaring observer",
        "",
        "For prime Fermat moduli F0..F4, the full residue state collapses to `2^n+1` future `x==-1` classes:",
        "",
        "| term | residues | observer classes | residue bits | observer bits | Pepin squarings |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for n, fermat_observer in enumerate(fermat):
        lines.append(
            f"| F{n} | {fermat_observer.source_states:,} | {fermat_observer.observer_classes:,} | {fermat_observer.source_bits} | {fermat_observer.observer_bits} | {(1 << n) - 1} |"
        )
    lines += [
        "",
        "In a prime Fermat field this class is the 2-adic valuation of the multiplicative-group exponent (plus one never-hit sink).  The class itself is tiny; extracting it from an arbitrary residue without already knowing order/factor information remains the hard projection.",
        "",
        "## Mersenne / Lucas--Lehmer observer",
        "",
        "For prime Mersenne moduli the exact `x -> x^2-2`, `x==0` observer has exactly p classes.  Composite M11 collapses differently and the initial state falls into the never-zero sink:",
        "",
        "| exponent | residues | observer classes | observer bits | initial class |",
        "|---:|---:|---:|---:|---:|",
    ]
    for e, mersenne_observer in zip((3, 5, 7, 11, 13), mersenne):
        lines.append(
            f"| {e} | {mersenne_observer.source_states:,} | {mersenne_observer.observer_classes:,} | {mersenne_observer.observer_bits} | {mersenne_observer.initial_class} |"
        )
    lines += [
        "",
        "The quadratic-unit conjugacy explains the prime case: the projection observer is an exponent-doubling depth class.  Again, observer state is logarithmic in modulus bitlength while extracting the class is not yet sublinear.",
        "",
        "## Production short-circuit from digit evolution",
        "",
        "The existing factored radix-word observer is now allowed to terminate special-number compilation before the longer modular recurrence when it proves a proper factor:",
        "",
        f"- F5: factor **{f5.factor_witness}**, skips **31** Pepin squarings and the duplicate digit-square path.",
        f"- M11: factor **{m11.factor_witness}**, skips **9** Lucas--Lehmer iterations.",
        f"- M23: factor **{m23.factor_witness}**, skips **21** Lucas--Lehmer iterations.",
        "- M31 has no bounded factor witness and therefore correctly falls through to Lucas--Lehmer.",
        "",
        "The important boundary is now explicit: projection observers can be dramatically smaller than arithmetic states, but the compiler only gains asymptotically when the observer class can itself be synthesized from the digit/factor coordinate before running the long evolution.",
    ]
    (
        report_output(
            "devtools.benchmarks.projection_observer_probe",
            "PROJECTION_OBSERVER_RESULTS.md",
        )
    ).write_text("\n".join(lines) + "\n")
    print(json.dumps(data, indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
