"""Deterministic limits audit for the radix-64 free Collatz consumer."""

from __future__ import annotations

from devtools.verification.consumer_fixtures import free_collatz_variables
import argparse
import json
from pathlib import Path
from typing import Protocol, cast

from number_compiler.arithmetic.carry.collatz_output_quotient import (
    RADIX64_FREE_CARRY_ACTIONS,
    RADIX64_FREE_GROWTH_TABLE,
    radix64_free_directional_row,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz import radix64_transducer
from number_compiler.sequences.collatz.output_morphism import (
    CollatzOutputMorphism,
)
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz


class _MutableRadix64TransducerModule(Protocol):
    Radix64CollatzStage: type[radix64_transducer.Radix64CollatzStage]


_WITNESSES = (
    (339, 2, 1929, 2249, 30, 35),
    (555, 2, 3209, 3529, 50, 55),
    (767, 2, 481, 801, 7, 12),
    (807, 3, 477, 797, 7, 12),
    (823, 4, 485, 805, 7, 12),
    (1442, 3, 557, 877, 8, 13),
    (1696, 3, 1853, 2173, 28, 33),
)


def _context_row(
    rows: tuple[tuple[tuple[tuple[int, int], ...], ...], ...], digit: int
) -> tuple[tuple[int, int], ...]:
    return tuple(rows[shift][carry][digit] for shift in range(6) for carry in range(3))


def _oracle(source: int, events: int) -> tuple[int, int]:
    value, valuation = source, 0
    for _ in range(events):
        step = accelerated_odd_collatz(value)
        value, valuation = step.target, valuation + step.valuation
    return value, valuation


def _streaming_metrics(events: int) -> dict[str, object]:
    original = radix64_transducer.Radix64CollatzStage
    stages: list[radix64_transducer.Radix64CollatzStage] = []
    counters = {"instances": 0, "feed_calls": 0, "finish_calls": 0, "peak": 0}

    def observe() -> None:
        live = sum(stage.pending is not None for stage in stages)
        counters["peak"] = max(counters["peak"], live)

    class TrackedStage(radix64_transducer.Radix64CollatzStage):
        def __init__(self) -> None:
            super().__init__()
            stages.append(self)
            counters["instances"] += 1

        def feed(self, digit: int) -> int | None:
            counters["feed_calls"] += 1
            result = super().feed(digit)
            observe()
            return result

        def finish(self) -> tuple[int, ...]:
            counters["finish_calls"] += 1
            result = super().finish()
            observe()
            return result

    module = cast(_MutableRadix64TransducerModule, radix64_transducer)
    module.Radix64CollatzStage = TrackedStage
    try:
        result = radix64_transducer.compose_radix64_events(digits_lsd(27, 64), events)
    finally:
        module.Radix64CollatzStage = original
    expected, valuation = _oracle(27, events)
    return {
        "events": events,
        "observed_stage_instances": counters["instances"],
        "observed_feed_calls": counters["feed_calls"],
        "observed_finish_calls": counters["finish_calls"],
        "observed_peak_live_pending_slots": counters["peak"],
        "final_pending_values": tuple(stage.pending for stage in stages),
        "target_matches_oracle": result.target_digits == digits_lsd(expected, 64),
        "valuation_matches_oracle": result.valuation == valuation,
        "intermediate_digit_word_collections": {
            "value": 0,
            "measurement": "structural: pipeline passes one emitted digit at a time",
        },
        "powered_free_consumer_action_nodes": None,
    }


def _free_function_metrics() -> dict[str, int]:
    ledger = ResourceLedger(max_nodes=200000)
    bits = BitFunctionArena(ledger)
    morphism = CollatzOutputMorphism(bits)
    ports, digit, carry, shift = free_collatz_variables(bits)
    outputs = morphism.free_directional_actions(digit, carry, shift)
    return {
        "factored_function_nodes": len(bits.nodes),
        "semantic_boolean_nodes": len(bits.functions.nodes),
        "retained_ledger_nodes": ledger.nodes,
        "retained_ledger_entries": ledger.entries,
        "output_count": len(outputs),
        "max_external_port_arity": max(
            len(bits.resolve(output).signature.inputs) for output in outputs
        ),
    }


def report() -> dict[str, object]:
    rows = tuple(
        tuple(radix64_free_directional_row(shift, carry) for carry in range(3))
        for shift in range(6)
    )
    fixed = tuple(
        tuple(
            len({rows[shift][carry][digit] for digit in range(64)})
            for carry in range(3)
        )
        for shift in range(6)
    )
    free_rows = {_context_row(rows, digit) for digit in range(64)}
    witnesses = []
    for old_class, shift, source_a, source_b, digit_a, digit_b in _WITNESSES:
        action_a = tuple(rows[shift][carry][digit_a] for carry in range(3))
        action_b = tuple(rows[shift][carry][digit_b] for carry in range(3))
        witnesses.append(
            {
                "old_class": old_class,
                "shift": shift,
                "source_delta": source_b - source_a,
                "digit_delta": digit_b - digit_a,
                "first_consumer_action": action_a,
                "second_consumer_action": action_b,
                "separated": action_a != action_b,
            }
        )
    temporal = tuple(_streaming_metrics(events) for events in (1, 2, 4, 8, 16, 32))
    return {
        "free_context": {
            "ternary_action_alphabet": len(RADIX64_FREE_CARRY_ACTIONS),
            "fixed_shift_carry_fiber_counts": fixed,
            "fixed_shift_profile": tuple(row[0] for row in fixed),
            "all_context_distinct_leaf_rows": len(free_rows),
            "all_context_is_semantic_leaf_quotient": False,
            "primitive_function_dag": _free_function_metrics(),
        },
        "growth": {
            "table": RADIX64_FREE_GROWTH_TABLE,
            "nonzero_contexts": tuple(
                (shift, carry, value)
                for shift, row in enumerate(RADIX64_FREE_GROWTH_TABLE)
                for carry, value in enumerate(row)
                if value
            ),
        },
        "workbook_witnesses": witnesses,
        "existing_temporal_pipeline": temporal,
        "closure": {
            "free_consumer_powering_implemented": False,
            "exact_root_occurrence_retained": True,
            "omega9_promoted_to_root_identity": False,
            "obstruction": (
                "the existing streaming pipeline retains one exact directional "
                "quotient slot per event; no recursive ConsumerResidualID exists"
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    payload = report()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
