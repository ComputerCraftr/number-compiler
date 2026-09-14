from __future__ import annotations

import json
from typing import TYPE_CHECKING

from devtools.experiments.power_numbers.special_successor_generators import (
    metrics_as_jsonable,
    special_successor_generator_metrics,
)
from devtools.paths import report_output, repository_root

if TYPE_CHECKING:
    from devtools.experiments.power_numbers.special_successor_models import (
        SpecialSuccessorGeneratorMetrics,
    )


ROOT = repository_root()

REPORT = report_output(
    "devtools.benchmarks.special_successor_generator_probe",
    "SPECIAL_SUCCESSOR_GENERATOR_RESULTS.md",
)
METRICS = ROOT / "results" / "special_successor_generator_metrics.json"


def markdown(
    metrics: SpecialSuccessorGeneratorMetrics | None = None,
) -> str:
    """Render a concise human summary; JSON retains the exhaustive tables."""
    m = special_successor_generator_metrics() if metrics is None else metrics
    guard = m.composite_depth_semantics
    lines = [
        "# Special-number group-depth / successor audit — concise summary",
        "",
        "## Result",
        "",
        f"- Successor-image filtration controls: **{len(m.filtrations)}**.",
        f"- Cheap residue/field controls: **{len(m.residue_constraints)}**.",
        f"- Prime-conditional group-depth controls: **{len(m.prime_group_depths)}**.",
        "- On independently verified prime fixtures, exact Moore behavior matches nested image depth; composite M11 is the fail-closed counterexample.",
        "- Carry/radix histories are refinements used for theorem discovery; exact minimization removes their redundant phase on prime controls.",
        "- Static cross-base/Jacobi, Boolean, and structured-automaton features do not provide a compact factor-free middle-depth injector.",
        "- Once the 2-primary depth coordinate is known, existing binary morphism machinery powers it logarithmically.",
        "",
        "## Composite guard",
        "",
        f"- M11 image ranks: `{','.join(map(str, guard.image_ranks))}`.",
        f"- M11 Moore classes: **{guard.moore_classes}**; image-depth classes: **{guard.image_depth_classes}**.",
        f"- M11 never-target states: **{guard.never_target_states}**; the canonical source has no prime-style `D-depth` target law.",
        "",
        "## Bounded composite short-circuits",
        "",
    ]
    for row in m.factor_short_circuits:
        witness = (
            "none"
            if row.witness_factor is None
            else f"k={row.witness_k}, q={row.witness_factor}"
        )
        lines.append(
            f"- {row.family} {row.parameter}: budget {row.candidate_budget}, "
            f"status `{row.status}`, witness `{witness}`, "
            f"powered compositions {row.batched_powered_compositions}."
        )
    lines += [
        "",
        "## Frontier",
        "",
        "- Factor-backed CRT truth remains research instrumentation only.",
        "- The incomplete factor-window shortcut can prove some composites but exhaustion remains `UNKNOWN`; it cannot certify purity.",
        "- The remaining constructor must derive the compact 2-primary purity/depth state directly from the unfactored candidate.",
        "- Production special-number resolution remains theorem-lazy and classically capped; this report does not define the production fallback.",
        "",
        "## Evidence",
        "",
        "- Full machine-readable tables: `results/special_successor_generator_metrics.json`.",
        "- Reproduce: `python -m devtools.benchmarks.special_successor_generator_probe`.",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    metrics_obj = special_successor_generator_metrics()
    report = markdown(metrics_obj)
    metrics = metrics_as_jsonable(metrics_obj)
    REPORT.write_text(report)
    METRICS.parent.mkdir(parents=True, exist_ok=True)
    METRICS.write_text(json.dumps(metrics, indent=2, sort_keys=True) + "\n")
    print(report, end="")


if __name__ == "__main__":
    main()
