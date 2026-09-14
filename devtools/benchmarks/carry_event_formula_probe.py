"""Release probe for the restored fixed-height carry/event compiler IR."""

from __future__ import annotations

import json
from typing import TypedDict

from devtools.paths import report_output, repository_root
from number_compiler.arithmetic.carry.event_memory import (
    carry_field,
    event_memory_horizon,
    forcing_event,
    forcing_event_from_carry,
    growths_from_event_widths,
    next_carry_from_window,
    next_event_from_window,
    pair_step,
    reconstruct_pair_from_carry_window,
    reconstruct_pair_from_event_window,
)
from number_compiler.arithmetic.formula.event_formula import (
    carry_event_formula_metrics,
    carry_event_formula_view,
)
from number_compiler.arithmetic.formula.formula import FormulaArena, root_from_values
from number_compiler.arithmetic.formula.summary import (
    register_summary,
    summary_from_values,
)
from number_compiler.arithmetic.formula.types import RadixSpec

HERE = repository_root()


def _orbit(
    steps: int = 1025,
) -> tuple[
    list[tuple[int, ...]],
    list[tuple[int, ...]],
    list[tuple[int, ...]],
    list[int],
    set[int],
    int,
]:
    source: tuple[int, ...] = (7, 18, 7)
    states = [source]
    carries = []
    events = []
    growths = []
    event_values: set[int] = set()
    max_growth_run = run = 0
    for _ in range(steps):
        carry = carry_field(source, base=10)
        target, growth = pair_step(source, 10)
        event = forcing_event(source, target, growth)
        assert event == forcing_event_from_carry(carry, base=10)
        assert len(event) == len(target)
        carries.append(carry)
        events.append(event)
        growths.append(growth)
        event_values.update(event)
        if growth:
            run += 1
            max_growth_run = max(max_growth_run, run)
        else:
            run = 0
        source = target
        states.append(source)
    return states, carries, events, growths, event_values, max_growth_run


class CarryFormulaReport(TypedDict):
    base: int
    seed_pair: list[int]
    pair_plane_bits: int
    fixed_temporal_height: int
    event_alphabet_seen_through_1025: list[int]
    max_consecutive_growth_seen: int
    event_is_function_of_single_forward_carry: bool
    reverse_carry_is_reflection_only: bool
    length_is_event_width: bool
    formula_ir: dict[str, object]
    exact_reconstruction_checkpoints: list[dict[str, object]]
    preferred_remaining_object: str
    not_preferred_remaining_object: str


def build_report() -> CarryFormulaReport:
    H = event_memory_horizon(10)
    states, carries, events, growths, event_values, max_growth_run = _orbit()
    checkpoints: list[dict[str, object]] = []
    for t in (H, 64, 128, 256, 512, 1024):
        ew = events[t - H : t]
        cw = carries[t - H : t]
        assert reconstruct_pair_from_event_window(ew, base=10) == states[t]
        assert reconstruct_pair_from_carry_window(cw, base=10) == states[t]
        assert growths_from_event_widths(ew) == tuple(growths[t - H + 1 : t])
        assert next_event_from_window(ew, base=10) == events[t]
        assert next_carry_from_window(cw, base=10) == carries[t]
        checkpoints.append(
            {
                "step": t,
                "endpoint_width": len(states[t]),
                "carry_fields": H,
                "old_pair_state_required": False,
                "separate_growth_stream_required": False,
                "event_widths_recover_later_growths": True,
            }
        )

    arena = FormulaArena()
    spec = RadixSpec(10)
    source = (7, 18, 7)
    root = root_from_values(source, arena, spec)
    register_summary(arena, root, spec, summary_from_values(source, spec))
    _target, growth = pair_step(source, 10)
    view = carry_event_formula_view(arena, root, spec, growth=growth)
    formula: dict[str, object] = dict(carry_event_formula_metrics(view))
    formula["event_values"] = list(view.event_values)
    formula["semantic_state_roots_created"] = 0

    report: CarryFormulaReport = {
        "base": 10,
        "seed_pair": list(source),
        "pair_plane_bits": 5,
        "fixed_temporal_height": H,
        "event_alphabet_seen_through_1025": sorted(event_values),
        "max_consecutive_growth_seen": max_growth_run,
        "event_is_function_of_single_forward_carry": True,
        "reverse_carry_is_reflection_only": True,
        "length_is_event_width": True,
        "formula_ir": formula,
        "exact_reconstruction_checkpoints": checkpoints,
        "preferred_remaining_object": "fixed-height binary carry slab with growing spatial grammar",
        "not_preferred_remaining_object": "unbounded tower of T^8/T^16/... canonical program syntax",
    }
    return report


def _write_results(report: CarryFormulaReport) -> None:
    (
        report_output(
            "devtools.benchmarks.carry_event_formula_probe",
            "carry_event_formula_metrics.json",
        )
    ).write_text(json.dumps(report, indent=2) + "\n")
    H = int(report["fixed_temporal_height"])
    formula = report["formula_ir"]
    md = f"""# Restored carry-event / length formulas — v0.10.0\n\nThe canonical tree again exposes the exact nonlinear forcing decomposition\n\n```text\nS_(t+1) = A_g S_t + E_t\nA_0 = 2\nA_1 = 1+z\n```\n\nwithout restoring any parallel semantic state. `X_v`, forward carry `C`, carry border,\nand the signed event-value position sets are hash-consed derived `Expr`/position-set views of the FormulaRoot planes.\n\n## Fixed temporal memory\n\nFor decimal, `w=bit_length(18)=5` and `H=4w={H}`. The release verifies at\nsteps 20, 64, 128, 256, 512 and 1024 that the previous **20** event fields reconstruct\nthe exact endpoint pair, and that the previous 20 forward binary carry fields do the same.\nNo older pair state, separate reverse-carry state or separate growth stream is required.\n\nEvent widths are exact lengths: `len(E_t)=len(S_(t+1))`, so successive event-width\ndifferences recover the later growth bits in the window.\n\n## Carry-only event formula\n\nNo growth:\n\n```text\nE_i = C_i + C_(d-i-1) - b(C_(i+1)+C_(d-i))\n```\n\nGrowth edges:\n\n```text\nE_0 = E_d = 1-b*C_1\n```\n\nGrowth interior:\n\n```text\nE_i = C_i + C_(d-i) - b(C_(i+1)+C_(d-i+1))\n```\n\nThe current source `(7,18,7)` event Formula IR uses **{formula["nodes"]}** reachable\nBoolean DAG nodes across all `X_v`, carry/border and event-value masks, and creates\n**zero semantic FormulaRoots**.\n\n## Architectural consequence\n\nThe remaining nonlinear target is no longer conceptually an unbounded temporal tower. It is\n\n```text\n20 binary carry position-set fields x growing spatial coordinate\n```\n\nThe earlier T^8+ canonical-program machinery remains an exact execution path, but the research\nquotient should now be formulated over this fixed-height carry slab. Full J remains fail-closed\nuntil that spatial grammar has a proved compact behavioral closure.\n"""
    (
        report_output(
            "devtools.benchmarks.carry_event_formula_probe",
            "CARRY_EVENT_FORMULA_RESULTS.md",
        )
    ).write_text(md)


def main() -> None:
    report = build_report()
    _write_results(report)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
