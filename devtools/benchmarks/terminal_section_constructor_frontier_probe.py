"""Reproducible report for the final Frobenius section-constructor frontier."""

from __future__ import annotations

from devtools.paths import report_directory

import json

from devtools.experiments.power_numbers.terminal_section_constructor_frontier import (
    FermatHighTwoAdicAKSTradeoff,
    cyclotomic_section_equivalence,
    fermat_high_two_adic_aks_tradeoff,
    section_constructor_frontier,
)
from devtools.paths import report_output, repository_root

ROOT = repository_root()


def main() -> None:
    RESULTS = report_directory(
        "devtools.benchmarks.terminal_section_constructor_frontier_probe"
    )
    RESULTS.mkdir(exist_ok=True)
    eq = [
        cyclotomic_section_equivalence("fermat", 4),
        cyclotomic_section_equivalence("mersenne", 13),
    ]
    trade: list[FermatHighTwoAdicAKSTradeoff] = []
    for n in (4, 16):
        trade.extend(fermat_high_two_adic_aks_tradeoff(n))
    frontier = [
        section_constructor_frontier("fermat", 4),
        section_constructor_frontier("mersenne", 13),
    ]
    from dataclasses import asdict

    payload = {
        "orbit_polynomial_section_equivalence": [asdict(r) for r in eq],
        "fermat_high_two_adic_aks_tradeoff": [asdict(r) for r in trade],
        "frontier": [asdict(r) for r in frontier],
    }
    (RESULTS / "terminal_section_constructor_frontier_metrics.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n"
    )

    lines = [
        "# Terminal section-constructor frontier",
        "",
        "The binary section law and its temporal powering are closed.  This pass",
        "checks whether low-degree cyclotomic orbit polynomials or the high-2-adic",
        "AKS/Berrizbeitia tradeoff supply the missing candidate-derived source.",
        "",
        "## Orbit-polynomial section",
        "",
        "| family | degree | current coordinate | section equation | new constructor? |",
        "|---|---:|---|---|---|",
    ]
    for r in eq:
        lines.append(
            f"| {r.family} | {r.frobenius_degree} | `{r.current_coordinate}` | "
            f"`{r.section_equation}` | {r.candidate_derived_section_constructor_known} |"
        )
    lines += [
        "",
        "Thus conductor doubling in the degree-1 Fermat representation is exactly",
        "square-root extraction in `Z/NZ`; in the degree-2 Mersenne trace",
        "representation it is exactly the half-angle square-root `U^2=T+2`.",
        "The orbit polynomial is therefore an exact re-expression of the existing",
        "quadratic-etale selector, not a new source projection.",
        "",
        "## Fermat high-2-adic AKS/Berrizbeitia endpoint tradeoff",
        "",
        "Write `F_n-1=2^K`, `K=2^n`.  Two exact endpoints are:",
        "",
        "| n | endpoint | u | power squarings | log2 polynomial degree | compact? |",
        "|---:|---|---:|---:|---:|---|",
    ]
    for tradeoff in trade:
        lines.append(
            f"| {tradeoff.parameter} | {tradeoff.endpoint} | {tradeoff.u} | "
            f"{tradeoff.power_condition_squaring_depth} | {tradeoff.polynomial_degree_log2} | "
            f"{tradeoff.compact_section_constructor} |"
        )
    lines += [
        "",
        "At `u=1` the polynomial side is only `K^2` degree, but the prerequisite",
        "power condition is the full Pepin-length `K-1` chain.  Choosing base 2",
        "and `u=K-n` makes the power condition the defining identity",
        "`2^(2^n)=-1 mod F_n`, but raises the polynomial degree to `2^(2K-2)`.",
        "Neither endpoint is a bit-length-of-horizon section quotient.",
        "",
        "## Remaining theorem",
        "",
        "The surviving operation is still exactly:",
        "",
        "```text",
        "unfactored sparse special candidate",
        "    -> candidate-derived ZERO / ONE / natural SPLIT",
        "       for one quadratic-etale section equation",
        "    -> shared binary section morphism",
        "```",
        "",
        "No production selector is promoted by this research result.",
    ]
    (
        report_output(
            "devtools.benchmarks.terminal_section_constructor_frontier_probe",
            "TERMINAL_SECTION_CONSTRUCTOR_FRONTIER.md",
        )
    ).write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
