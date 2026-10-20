from __future__ import annotations

import json

from devtools.experiments.algebra.residue_refined_bend import fast_multipoint_bend_audit
from devtools.paths import report_output
from devtools.verification.collatz_frame_projection import (
    collatz_affine_suffix_event_power_word,
)
from number_compiler.arithmetic.automata.program_word import from_runs
from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache
from number_compiler.sequences.collatz.power import CollatzEventArena


def _bsgs_rows() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for family, parameter, span in (
        ("fermat", 5, 511),
        ("mersenne", 29, 399),
    ):
        audit = fast_multipoint_bend_audit(
            family,
            parameter,
            start=1,
            span=span,
        )
        rows.append(
            {
                "family": family,
                "parameter": parameter,
                "span": span,
                "exact": audit.exact,
                "support_gcd": audit.bend_support_gcd,
                "raw_progression_states": audit.raw_progression_states,
                "algebraic_progression_shapes": audit.algebraic_progression_shapes,
                "algebraic_progression_compression": audit.algebraic_progression_compression,
                "algebraic_shape_cache_hits": audit.algebraic_shape_cache_hits,
                "algebraic_shape_cache_misses": audit.algebraic_shape_cache_misses,
                "absolute_coefficient_cache_hits": audit.morphism_cache_hits,
                "absolute_coefficient_cache_misses": audit.morphism_cache_misses,
                "charged_total_ring_ops": audit.charged_total_ring_ops,
                "polylogarithmic_in_span": audit.polylogarithmic_in_span,
            }
        )
    return rows


def _collatz_frame_pair() -> dict[str, object]:
    cache = CollatzGermTransitionCache()
    arena = CollatzEventArena()
    rows: list[dict[str, object]] = []
    for q in (100, 1_000_000):
        word = from_runs(((1, q), (3, 1)))
        before = cache.metrics()
        projection = collatz_affine_suffix_event_power_word(
            word,
            2,
            arena=arena,
            transition_cache=cache,
        )
        after = cache.metrics()
        rows.append(
            {
                "frame_depth": q,
                "total_shift": projection.root.effect.shift,
                "target": {
                    "multiplier": projection.target.multiplier,
                    "offset": projection.target.offset,
                    "logical_steps": projection.target.logical_steps,
                },
                "transition_misses_added": after["canonical_misses"]
                - before["canonical_misses"],
                "transition_hits_added": after["canonical_hits"]
                - before["canonical_hits"],
            }
        )
    return {
        "rows": rows,
        "final_cache": cache.metrics(),
        "event_arena_nodes": arena.node_count,
        "cocycle_materializations": arena.cocycle_materializations,
    }


def main() -> None:
    data = {
        "bsgs": _bsgs_rows(),
        "collatz": _collatz_frame_pair(),
        "claims": {
            "cache_lookup_precedes_absolute_bsgs_translation": True,
            "bsgs_algebraic_shape_quotients_translation": True,
            "bsgs_unit_step_scale_is_algebraic_action": True,
            "bsgs_absolute_coefficient_lowering_still_charged": True,
            "bsgs_first_evaluation_polylogarithmic": False,
            "collatz_cache_lookup_precedes_valuation_emission": True,
            "collatz_matching_root_prefix_is_gauge_action": True,
            "collatz_logical_time_not_in_transition_key": True,
            "collatz_future_event_count_polylogarithmic": False,
        },
    }
    text = json.dumps(data, indent=2, sort_keys=True) + "\n"
    out = report_output(
        "devtools.benchmarks.early_algebraic_cache_probe",
        "early_algebraic_cache_metrics.json",
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
