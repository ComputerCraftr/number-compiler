"""Reproducible shared binary-handler / Frobenius source-projection audit."""

from __future__ import annotations

import json

from devtools.benchmarks.report_schema import record, records
from devtools.experiments.power_numbers.terminal_etale_square import (
    special_etale_tile_applicability_audit,
)
from devtools.experiments.power_numbers.terminal_projective_wreath import (
    ODOMETER_BINARY_HANDLER,
    candidate_frobenius_section_probe,
    odometer_section_step,
)
from devtools.paths import report_directory, report_output, repository_root
from number_compiler.arithmetic.fields.binary_piecewise import (
    BinaryBranchDecision,
    BinaryPiecewiseHandler,
)
from number_compiler.arithmetic.fields.digit_formula import digit_root_from_int
from number_compiler.arithmetic.formula.formula import FormulaArena
from number_compiler.sequences.collatz.orbit import (
    BINARY,
    COLLATZ_BINARY_HANDLER,
    COLLATZ_PIECEWISE_MORPHISM,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    prime_decision_chunk_spec,
    terminal_threshold_spec,
)

ROOT = repository_root()


def _collatz_row(value: int) -> dict[str, object]:
    arena = FormulaArena()
    root = digit_root_from_int(value, arena, BINARY)
    decision = COLLATZ_PIECEWISE_MORPHISM.branch_decision(arena, root)
    return {
        "value": value,
        "decision": decision.kind,
        "method": decision.method,
        "selected_branch": COLLATZ_PIECEWISE_MORPHISM.select_branch(arena, root),
    }


def _frobenius_row(family: str, parameter: int) -> dict[str, object]:
    spec = terminal_threshold_spec(family, parameter)
    if spec.prime_decision_level == 0:
        return {
            "family": family,
            "parameter": parameter,
            "structural_pass": True,
            "chunk": None,
        }
    chunk = prime_decision_chunk_spec(spec)
    applicability = special_etale_tile_applicability_audit(family, parameter)
    research = candidate_frobenius_section_probe(
        family,
        parameter,
        chunk.start_level,
        chunk.span,
    )
    return {
        "family": family,
        "parameter": parameter,
        "structural_pass": False,
        "chunk": {
            "start_level": chunk.start_level,
            "span": chunk.span,
            "required_local_v2": chunk.required_local_v2,
        },
        "production_status": applicability.production_status,
        "angular_action_key": applicability.angular_action_key,
        "selector_in_action_identity": applicability.selector_in_action_identity,
        "per_level_states_retained": applicability.per_level_states_retained,
        "research_section_status": research.status,
        "research_method": research.method,
        "factor_enumeration": research.factor_enumeration,
        "tree_nodes_materialized": research.tree_nodes_materialized,
        "one_level_replays": research.one_level_replays,
    }


def main() -> None:
    handler = BinaryPiecewiseHandler("probe")
    dispatch = {}
    for decision in (
        BinaryBranchDecision.zero("zero"),
        BinaryBranchDecision.one("one"),
        BinaryBranchDecision.split("split", 7),
        BinaryBranchDecision.unknown("unknown"),
    ):
        dispatch[decision.kind] = handler.dispatch(
            decision,
            zero_branch=lambda d: d.kind,
            one_branch=lambda d: d.kind,
            split_branch=lambda d: d.kind,
            unknown_branch=lambda d: d.kind,
        )

    special_candidates = [
        _frobenius_row("fermat", 4),
        _frobenius_row("fermat", 5),
        _frobenius_row("mersenne", 11),
        _frobenius_row("mersenne", 13),
    ]
    data: dict[str, object] = {
        "shared_handler": {
            "generic": handler.canonical_key,
            "collatz": COLLATZ_BINARY_HANDLER.canonical_key,
            "odometer_research": ODOMETER_BINARY_HANDLER.canonical_key,
            "dispatch_exact": dispatch,
        },
        "collatz": [_collatz_row(8), _collatz_row(9)],
        "odometer": [
            {
                "stride": k,
                "decision": odometer_section_step(k).decision.kind,
                "status": odometer_section_step(k).status,
                "next_stride": odometer_section_step(k).next_stride,
            }
            for k in (10, 5)
        ],
        "special_candidates": special_candidates,
        "conclusion": {
            "shared_binary_control_cleanup_complete": True,
            "frobenius_per_level_controller_removed": True,
            "angular_block_transport_closed": True,
            "candidate_root_action_extractor_available": False,
            "theorem_closed": False,
            "production_remains_fail_closed": True,
            "missing_edge": "unfactored sparse candidate -> ZERO/ONE/SPLIT Frobenius root action",
        },
    }
    out = (
        report_directory("devtools.benchmarks.terminal_binary_piecewise_probe")
        / "terminal_binary_piecewise_metrics.json"
    )
    out.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")

    rows = "\n".join(
        f"| {r['family']} | {r['parameter']} | "
        f"{('-' if r['chunk'] is None else record(r['chunk'])['span'])} | "
        f"{('ALL_PASS' if r['structural_pass'] else r['production_status'])} | "
        f"{('-' if r['structural_pass'] else 'output-selector-unavailable')} |"
        for r in records(special_candidates)
    )
    md = f"""# Shared binary piecewise cleanup / theorem-closure audit

The Collatz controller and research odometer use the domain-neutral
`BinaryPiecewiseHandler`.  The old production Frobenius per-level controller
has been removed: the terminal path already owns a whole powered germ block,
so publishing one state for every consumed level duplicated its temporal axis.

For Collatz, `ZERO/ONE` is derived from the current formula LSB.  The local
Frobenius odometer remains research-only.  Fermat/Mersenne production keeps a
single binary-powered angular transfer and an output-only etale selector.  The
selector is deliberately still unavailable: no supplied stride bit, factor
truth, or per-level replay is accepted.

| family | parameter | queried span | one-step status | method |
|---|---:|---:|---|---|
{rows}

## Closure status

- redundant production per-level section controller: **removed**;
- local angular block transport: **complete**;
- candidate-derived root action: **not proved**;
- production oracle/replay fallback: **none**.

The remaining theorem is exactly

```text
unfactored sparse special candidate
    -> candidate-derived etale selector / natural SPLIT support
    -> output port beside the powered angular tile action
```

A morphism that receives a supplied `k & 1`, factors the candidate, or computes
the root bit by replaying the Lucas/Pépin horizon is rejected.
"""
    (
        report_output(
            "devtools.benchmarks.terminal_binary_piecewise_probe",
            "TERMINAL_BINARY_PIECEWISE_RESULTS.md",
        )
    ).write_text(md)
    print(json.dumps(data, indent=2, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
