from __future__ import annotations

import json
from pathlib import Path
from typing import Literal

from devtools.experiments.algebra.baby_giant_behavioral_bend import (
    BabyGiantBendPacketMemo,
)
from devtools.experiments.algebra.residue_refined_bend import (
    FastMultipointBendAudit,
    fast_multipoint_bend_audit,
)
from devtools.proofs.collatz_frame_projection import (
    collatz_affine_suffix_event_power_word,
)
from number_compiler.arithmetic.automata.program_word import from_runs
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
from number_compiler.sequences.collatz.parity import (
    CollatzParityTimeOperator,
    CollatzValuationCursor,
    CollatzValuationSchedule,
)
from number_compiler.sequences.collatz.power import CollatzEventArena, CollatzPowerArena


def _collatz_event_control() -> dict[str, object]:
    source = 27
    value = source
    valuations: list[int] = []
    for _ in range(32):
        step = accelerated_odd_collatz(value)
        valuations.append(step.valuation)
        value = step.target

    event_arena = CollatzEventArena()
    event_root = event_arena.from_valuations(valuations)
    event_target = event_arena.apply_exact(event_root, source)

    branches: tuple[Literal["E", "O"], Literal["E", "O"]] = ("O", "E")
    expanded = tuple(
        branch
        for k in valuations
        for branch in (branches[0], *(branches[1] for _ in range(k)))
    )
    branch_arena = CollatzPowerArena()
    branch_root = branch_arena.from_branches(expanded)
    branch_target = branch_root.effect.apply(source)
    assert event_target == branch_target == value

    return {
        "seed": source,
        "events": len(valuations),
        "valuation_sum": sum(valuations),
        "expanded_branch_symbols": len(expanded),
        "event_compositions": event_arena.composition_operations,
        "expanded_branch_compositions": branch_arena.composition_operations,
        "event_metrics": event_arena.metrics(event_root),
        "targets_equal": True,
    }


def _large_collatz_control() -> dict[str, object]:
    q = 1_000_000
    word = from_runs(((1, q), (3, 1)))
    arena = CollatzEventArena()
    projection = collatz_affine_suffix_event_power_word(word, 2, arena=arena)
    metrics = arena.metrics(projection.root)

    single = CollatzEventArena()
    huge = single.event(q)
    huge_metrics = single.metrics(huge)

    schedule = CollatzValuationSchedule(0, (q,))
    position = CollatzParityTimeOperator(q // 2).apply_valuations(
        CollatzValuationCursor(schedule),
    )
    return {
        "radix4_sentinel_run": q,
        "two_event_total_shift": projection.root.effect.shift,
        "two_event_metrics": metrics,
        "single_million_valuation_metrics": huge_metrics,
        "single_million_valuation_expected_expanded_symbols": q + 1,
        "schedule": {
            "event_count": schedule.event_count,
            "normalized_symbols": schedule.normalized_symbols,
            "physical_steps": schedule.physical_steps,
            "description_bits": schedule.description_bits,
            "halfway_event_index": position.position.event_index,
            "halfway_event_offset": position.position.event_offset,
            "binary_search_bound": position.event_binary_search_bound,
        },
        "large_affine_cocycle_materialized": metrics["cocycle_materializations"] != 0,
    }


def _bsgs_control() -> dict[str, object]:
    f5 = fast_multipoint_bend_audit("fermat", 5, start=1, span=511)
    m29 = fast_multipoint_bend_audit("mersenne", 29, start=1, span=399)
    memo = BabyGiantBendPacketMemo()
    first = memo.evaluate("fermat", 5, start=1, span=511)
    second = memo.evaluate("fermat", 5, start=1, span=511)
    assert first is second

    def row(audit: FastMultipointBendAudit) -> dict[str, object]:
        return {
            "family": audit.family,
            "parameter": audit.parameter,
            "span": audit.span,
            "baby_width": audit.baby_width,
            "giant_blocks": audit.full_blocks,
            "support_gcd": audit.bend_support_gcd,
            "exact": audit.exact,
            "baby_morphism_description_bits": audit.baby_morphism_description_bits,
            "giant_morphism_description_bits": audit.giant_morphism_description_bits,
            "morphism_cache_hits": audit.morphism_cache_hits,
            "morphism_cache_misses": audit.morphism_cache_misses,
            "morphism_cached_coefficient_slots": audit.morphism_cached_coefficient_slots,
            "progression_root_lists_materialized": audit.progression_root_lists_materialized,
            "newton_precision_morphismized": audit.newton_precision_morphismized,
            "charged_total_ring_ops": audit.charged_total_ring_ops,
            "polylogarithmic_in_span": audit.polylogarithmic_in_span,
        }

    return {
        "controls": [row(f5), row(m29)],
        "fixed_window_packet_reuse": {
            "size": memo.size,
            "hits": memo.hits,
            "misses": memo.misses,
            "same_object": first is second,
        },
    }


def main() -> None:
    data = {
        "bsgs": _bsgs_control(),
        "collatz_event_transport": _collatz_event_control(),
        "collatz_large_run": _large_collatz_control(),
        "claims": {
            "bsgs_predictable_products_are_morphisms": True,
            "bsgs_heavy_coefficients_lowered_lazily": True,
            "bsgs_first_evaluation_polylogarithmic": False,
            "collatz_forced_even_branch_expansion_removed": True,
            "collatz_parity_word_required_for_valuation_schedule": False,
            "collatz_multi_event_affine_offset_eagerly_materialized": False,
            "collatz_future_event_count_polylogarithmic": False,
        },
    }
    text = json.dumps(data, indent=2, sort_keys=True) + "\n"
    out = Path("results/morphism_cleanup_metrics.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
