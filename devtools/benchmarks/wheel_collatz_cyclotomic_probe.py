"""Deterministic v0.29 prime-wheel / self-branching Collatz probe."""

from __future__ import annotations

from devtools.paths import report_directory

import json

from devtools.benchmarks.report_schema import sequence
from devtools.paths import report_output, repository_root
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import PrimeBlockSequenceSpec
from number_compiler.arithmetic.functions.finite_unary import analyze_observer
from number_compiler.arithmetic.polynomials.cyclotomic_family import (
    collatz_piecewise_cyclotomic_step,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock

ROOT = repository_root()


def collatz_successor(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def component_key(
    n: int, orders: tuple[int, ...], modulus: int = 32
) -> tuple[int | tuple[int, ...], ...]:
    return (n & 1,) + tuple(
        CyclotomicDigitBlock.from_radix_value(
            n,
            base=2,
            order=order,
            modulus=modulus,
        ).residue
        for order in orders
    )


def main() -> int:
    compiler = CanonicalSequenceCompiler()
    prime_rows = []
    for length in (64, 256, 1024, 4096):
        got = compiler.compile_diagnostic(PrimeBlockSequenceSpec(9_999_993, length))
        auto = got.automaton
        if auto is None or got.decision.wheel_cyclotomic is None:
            raise AssertionError("diagnostic prime compilation omitted automata")
        wheel = got.decision.wheel_cyclotomic
        # Exhaustive classification on smaller blocks; the 4096 block is
        # already cross-checked at the exact first hole and by lane semantics.
        exact_points = length
        for index in range(exact_points):
            prime, _calls = wheel.classify_index(index)
            # decision terminal lookup is intentionally not materialized here;
            # the residual projector summary and wheel share the same lane basis.
            value = 9_999_993 + 2 * index
            from number_compiler.sequences.prime.set import smallest_factor

            if prime != (smallest_factor(value) is None):
                raise AssertionError((length, index, value))
        packed_charged = 2 * auto.total_group_bits
        cyclo_charged = auto.cyclotomic_state_bits + auto.cyclotomic_descriptor_bits
        prime_rows.append(
            {
                "length": length,
                "lanes": got.decision.canonical_lanes,
                "packed_groups": auto.group_count,
                "packed_state_bits": auto.total_group_bits,
                "packed_charged_bits": packed_charged,
                "cyclotomic_groups": auto.cyclotomic_group_count,
                "cyclotomic_state_bits": auto.cyclotomic_state_bits,
                "cyclotomic_descriptor_bits": auto.cyclotomic_descriptor_bits,
                "cyclotomic_charged_bits": cyclo_charged,
                "selected": auto.selected_random_access,
                "first_index": auto.first_index,
                "packed_first_calls": auto.first_gcd_calls,
                "cyclotomic_first_calls": auto.cyclotomic_first_calls,
                "prime_field_candidates": auto.cyclotomic_prime_candidates,
                "root_trials": auto.cyclotomic_root_trials,
                "exact_points": exact_points,
            }
        )

    # The physical Collatz successor manufactures its own branch.  Audit the
    # shared polynomial/local-ring implementation on a complete bounded source.
    limit = 4096
    exact_steps = 0
    even_steps = odd_steps = 0
    for n in range(1, limit + 1):
        step = collatz_piecewise_cyclotomic_step(n, order=8, modulus=32)
        if step.target_value != collatz_successor(n) or not step.exact:
            raise AssertionError((n, step))
        exact_steps += 1
        even_steps += int(step.branch == "divide_2")
        odd_steps += int(step.branch == "multiply_3_add_1")

    closure_rows = []
    for orders in ((4,), (8,), (16,), (5, 7)):
        current = tuple(component_key(n, orders) for n in range(1, limit + 1))
        nxt = tuple(
            component_key(collatz_successor(n), orders) for n in range(1, limit + 1)
        )
        audit = analyze_observer(current, nxt)
        closure_rows.append(
            {
                "orders": list(orders),
                "classes": audit.classes,
                "successor_conflicts": audit.successor_conflicts,
                "next_closed": audit.next_closed,
                "noninjective": audit.classes < limit,
            }
        )

    metrics = {
        "release": "v0.29.0",
        "prime": prime_rows,
        "collatz": {
            "bounded_sources": limit,
            "exact_piecewise_steps": exact_steps,
            "even_steps": even_steps,
            "odd_steps": odd_steps,
            "closure": closure_rows,
        },
    }
    outdir = report_directory("devtools.benchmarks.wheel_collatz_cyclotomic_probe")
    outdir.mkdir(exist_ok=True)
    (outdir / "wheel_collatz_cyclotomic_metrics.json").write_text(
        json.dumps(metrics, indent=2, sort_keys=True) + "\n"
    )

    lines = [
        "# Wheel-cyclotomic / self-branching Collatz results — v0.29.0",
        "",
        "## Prime wheel as a cyclotomic field automaton",
        "",
        (
            "Each finite divisor cycle `j == phase (mod q)` is represented by a root-of-unity projection. "
            "Several squarefree periods are packed into one field `F_P` with `prod(q) | P-1`; one live state `a^j` advances by multiplication and projects to every constituent q-th root subgroup. "
            "No prime bitmap or Boolean output jet is part of this automaton."
        ),
        "",
        "| candidates | lanes | packed groups | packed state bits | cyclotomic groups | cyclotomic state bits | cyclotomic descriptor bits | charged packed | charged cyclotomic | selected |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|",
    ]
    for row_1 in prime_rows:
        lines.append(
            f"| {row_1['length']:,} | {row_1['lanes']} | {row_1['packed_groups']} | {row_1['packed_state_bits']:,} | "
            f"{row_1['cyclotomic_groups']} | {row_1['cyclotomic_state_bits']:,} | {row_1['cyclotomic_descriptor_bits']:,} | "
            f"{row_1['packed_charged_bits']:,} | {row_1['cyclotomic_charged_bits']:,} | {row_1['selected']} |"
        )
    lines += [
        "",
        "The field coordinate is therefore a real block-specific random-access alternative, not a replacement theorem for the residual-divisor block projector. The compiler selects it only when state+descriptor charge beats the packed carrier; larger blocks currently cross back to the packed representation.",
        "",
        "## Collatz successor manufactures its own branch",
        "",
        f"All **{exact_steps:,}/{limit:,}** physical successors are exact in the shared cyclotomic digit layer ({even_steps:,} even, {odd_steps:,} odd). Even is `z^-1`; odd is `(1+z)D+1` followed by canonical binary normalization. No parity/valuation itinerary is an input to the operator.",
        "",
        "The normalized successor still does not descend to one small current cyclotomic component. Bounded closure audit:",
        "",
        "| components | classes / 4096 | successor conflicts | next-closed | non-injective |",
        "|---|---:|---:|---|---|",
    ]
    for row_2 in closure_rows:
        label = ",".join(f"Phi_{o}" for o in sequence(row_2["orders"]))
        lines.append(
            f"| {label} mod 32 + parity | {row_2['classes']} | {row_2['successor_conflicts']:,} | "
            f"{row_2['next_closed']} | {row_2['noninjective']} |"
        )
    lines += [
        "",
        "`Phi_5 + Phi_7` is conflict-free only because it is injective on this bounded source set; it is explicitly rejected as a state reduction. The useful architectural gain is that branch generation and cyclotomic transport are now one operator, so the remaining Collatz theorem is precisely a non-injective normalized quotient of that operator—not an unknown parity-word generator.",
        "",
    ]
    (
        report_output(
            "devtools.benchmarks.wheel_collatz_cyclotomic_probe",
            "WHEEL_COLLATZ_CYCLOTOMIC_RESULTS.md",
        )
    ).write_text("\n".join(lines))
    print(json.dumps(metrics, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
