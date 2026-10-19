"""Cold schema-seven M(N, X) measurements with explicit horizon ordering."""

from __future__ import annotations

import argparse
import itertools
import json
from collections.abc import Callable, Iterable
from dataclasses import asdict, dataclass
from time import perf_counter
from typing import Any

from number_compiler.resources.temporal_diagnostics import METRICS_SCHEMA_VERSION


@dataclass(frozen=True, slots=True)
class ColdFieldImageRow:
    family: str
    horizon: int
    order_index: int
    index_bits: int
    digit: int
    new_canonical_field_images_published: int
    field_image_nodes: int
    field_interface_nodes: int
    total_internal_action_work: int
    higher_concrete_operation_evaluations: int
    temporal_parent_compositions: int
    spatial_parent_evaluations: int
    retained_entries: int
    retained_nodes: int
    sequential_generation_advances: int
    whole_word_sweeps: int
    whole_word_symbol_visits: int
    proof_machine_applications: int
    forbidden_future_payloads: int
    resource_accounting_mismatch: int


def _validated_measurement_inputs(seed: int, horizon: int) -> tuple[int, int]:
    if type(seed) is not int or seed < 0 or seed.bit_length() > 1024:
        raise ValueError("research source must be nonnegative and at most 1024 bits")
    if type(horizon) is not int or not 0 <= horizon <= 1024:
        raise ValueError("research horizon must lie in 0..1024")
    return seed, horizon


def ordered_horizons(horizons: Iterable[int], order: str) -> tuple[int, ...]:
    values = tuple(horizons)
    if any(type(value) is not int or value < 0 for value in values):
        raise ValueError("cold horizons require nonnegative exact integers")
    if len(set(values)) != len(values):
        raise ValueError("cold horizons must be unique")
    if order == "ascending":
        return tuple(sorted(values))
    if order == "descending":
        return tuple(sorted(values, reverse=True))
    raise ValueError("cold order must be ascending or descending")


def cold_rows(
    family: str,
    constructor: Callable[[int], Any],
    horizons: Iterable[int],
    *,
    order: str,
) -> tuple[ColdFieldImageRow, ...]:
    """Measure each horizon on a distinct ledger, with no warmed predecessor."""
    rows: list[ColdFieldImageRow] = []
    ledgers: list[object] = []
    for order_index, horizon in enumerate(ordered_horizons(horizons, order)):
        term = constructor(horizon)
        if any(term.resource_ledger is previous for previous in ledgers):
            raise AssertionError("cold probe constructor reused an index ledger")
        ledgers.append(term.resource_ledger)
        digit = term.digit(0)
        metrics = term.metrics()
        if (
            metrics.metrics_schema_version != METRICS_SCHEMA_VERSION
            or metrics.forbidden_future_payloads
        ):
            raise AssertionError(("invalid-schema7-cold-snapshot", horizon, metrics))
        rows.append(
            ColdFieldImageRow(
                family,
                horizon,
                order_index,
                max(1, horizon.bit_length()),
                digit,
                metrics.new_canonical_field_images_published,
                metrics.field_image_nodes,
                metrics.field_interface_nodes,
                metrics.total_internal_action_work,
                getattr(metrics, "higher_concrete_operation_evaluations", 0),
                metrics.temporal_parent_compositions,
                metrics.spatial_parent_evaluations,
                metrics.resource_ledger_entries,
                metrics.resource_ledger_nodes,
                metrics.sequential_generation_advances,
                metrics.whole_word_sweeps,
                metrics.whole_word_symbol_visits,
                metrics.proof_machine_applications,
                metrics.forbidden_future_payloads,
                metrics.resource_accounting_mismatch,
            )
        )
    return tuple(rows)


def cold_measurement(
    family: str,
    constructor: Callable[[int], Any],
    horizons: Iterable[int],
    *,
    order: str,
) -> dict[str, object]:
    """Return rows only when the certified executor completed every query."""
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

    try:
        rows = cold_rows(family, constructor, horizons, order=order)
    except UnsupportedInterfaceError as error:
        return {
            "status": "unavailable",
            "measurements_complete": False,
            "rows": [],
            "rejection_type": type(error).__name__,
            "rejection_reason": str(error),
        }
    ordered = sorted(rows, key=lambda row: row.horizon)
    bootstrap = ordered[0].total_internal_action_work if ordered else 0
    work_within_doubling_envelope = all(
        current.horizon != 2 * previous.horizon
        or current.total_internal_action_work
        <= 2 * previous.total_internal_action_work + bootstrap
        for previous, current in itertools.pairwise(ordered)
    )
    higher_work_within_doubling_envelope = all(
        current.horizon != 2 * previous.horizon
        or current.higher_concrete_operation_evaluations
        <= 2 * previous.higher_concrete_operation_evaluations + 64
        for previous, current in itertools.pairwise(ordered)
    )
    forbidden_work_zero = all(
        row.sequential_generation_advances == 0
        and row.whole_word_sweeps == 0
        and row.whole_word_symbol_visits == 0
        and row.proof_machine_applications == 0
        and row.forbidden_future_payloads == 0
        and row.resource_accounting_mismatch == 0
        for row in rows
    )
    temporal_composition_gate = all(
        row.temporal_parent_compositions <= 2 * row.index_bits + 4 for row in rows
    )
    recursive_images_published = bool(rows) and all(
        row.new_canonical_field_images_published > 0 and row.field_image_nodes > 0
        for row in rows
    )
    blockers = []
    if not forbidden_work_zero:
        blockers.append("forbidden_execution_work_observed")
    if not temporal_composition_gate:
        blockers.append("temporal_composition_exceeds_binary_envelope")
    if not recursive_images_published:
        blockers.append("certified_path_published_no_recursive_field_images")
    if not work_within_doubling_envelope:
        blockers.append("internal_action_work_exceeds_doubling_envelope")
    if not higher_work_within_doubling_envelope:
        blockers.append("higher_interface_work_exceeds_doubling_envelope")
    return {
        "status": "GREEN" if not blockers else "RED",
        "measurements_complete": True,
        "rows": [asdict(row) for row in rows],
        "measured_scaling_gate": "PASS" if not blockers else "BLOCKED",
        "release_blockers": blockers,
        "successor_closure_proved": False,
        "exact_bimachine_composition_available": True,
        "closure_field_scope": "legacy source-independent finite temporal quotient; not executor availability",
    }


def run_probe(
    order: str = "both",
    *,
    horizons: Iterable[int] | None = None,
) -> dict[str, object]:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    orders = ("ascending", "descending") if order == "both" else (order,)
    measured_horizons = (
        (16, 32, 64, 128, 256, 512, 1024) if horizons is None else tuple(horizons)
    )
    results: dict[str, object] = {}
    for current in orders:
        results[current] = {
            "reverse": cold_measurement(
                "reverse-add",
                lambda n: ReverseAddPoweredTerm(196, n),
                measured_horizons,
                order=current,
            ),
            "collatz": cold_measurement(
                "collatz",
                lambda n: PoweredCollatzTerm(27, n),
                measured_horizons,
                order=current,
            ),
        }
    complete = all(
        bool(family["measurements_complete"])
        for order_result in results.values()
        if isinstance(order_result, dict)
        for family in order_result.values()
        if isinstance(family, dict)
    )
    green = complete and all(
        family["status"] == "GREEN"
        for order_result in results.values()
        if isinstance(order_result, dict)
        for family in order_result.values()
        if isinstance(family, dict)
    )
    return {
        "metrics_schema_version": METRICS_SCHEMA_VERSION,
        "cold_index_scope": "fresh-per-row",
        "orders": results,
        "status": "GREEN" if green else ("RED" if complete else "unavailable"),
        "measurements_complete": complete,
        "logarithmic_execution_claim": False,
        "successor_closure_proved": False,
        "exact_bimachine_composition_available": True,
        "closure_field_scope": "legacy source-independent finite temporal quotient; not executor availability",
    }


def research_pair_measurement(seed: int, horizon: int) -> dict[str, object]:
    """Bounded cold spatial-grammar trial; never production acceptance.

    Each invocation has a fresh arena. Count retained construction, not only
    the final reachable graph, and keep rendering/reference timings separate.
    """
    from devtools.experiments.reverse_add.pair_slp_transducer import PairSLPTransducer
    from number_compiler.resources.ledger import ResourceLedger

    seed, horizon = _validated_measurement_inputs(seed, horizon)
    ledger = ResourceLedger()
    grammar = PairSLPTransducer(ledger)
    try:
        started = perf_counter()
        digits = grammar.word(tuple(map(int, reversed(str(seed)))))
        pair = grammar.pair_from_digits(digits)
        previous = pair
        for _ in range(horizon):
            previous = pair
            step = grammar.successor(pair)
            digits, pair = step.digit_root, step.pair_root
        construction_seconds = perf_counter() - started
        counters = dict(ledger.counters)
        retained_nodes, entries = grammar.node_count, ledger.entries
        retained_ledger_nodes = ledger.nodes
        started = perf_counter()
        reachable = len(grammar.reachable(pair))
        width = grammar.node(digits).length
        observation_seconds = perf_counter() - started
        observation_counters = {
            key: value - counters.get(key, 0)
            for key, value in ledger.counters.items()
            if value != counters.get(key, 0)
        }
        started = perf_counter()
        output: list[str] = []
        stack = [digits]
        while stack:
            node = grammar.node(stack.pop())
            if node.kind == "TERM":
                if not 0 <= node.symbol <= 9:
                    raise AssertionError("normalized output left decimal alphabet")
                output.append(str(node.symbol))
            elif node.kind == "CONCAT":
                stack.extend((node.right, node.left))
            elif node.kind == "REPEAT":
                stack.extend([node.child] * node.count)
        rendered = "".join(reversed(output))
        rendering_seconds = perf_counter() - started
        started = perf_counter()
        reference = seed
        for _ in range(horizon):
            reference += int(str(reference)[::-1])
        if rendered != str(reference) or width != len(rendered):
            raise AssertionError("spatial grammar disagrees with bounded reference")
        reference_seconds = perf_counter() - started
        before_warm = dict(ledger.counters)
        started = perf_counter()
        if horizon:
            warm = grammar.successor(previous)
            if warm.pair_root != pair or warm.digit_root != digits:
                raise AssertionError("warm demand changed the exact grammar result")
        warm_seconds = perf_counter() - started
        return {
            "scope": "research-spatial-grammar-not-production",
            "seed": seed,
            "horizon": horizon,
            "cache_scope": "fresh-per-trial; no process cache used",
            "chronological_successors": horizon,
            "construction_seconds": construction_seconds,
            "observation_seconds": observation_seconds,
            "rendering_seconds": rendering_seconds,
            "reference_seconds": reference_seconds,
            "warm_last_demand_seconds": warm_seconds,
            "warm_new_nodes": grammar.node_count - retained_nodes,
            "width": width,
            "value": rendered,
            "retained_grammar_nodes": retained_nodes,
            "retained_ledger_entries": entries,
            "retained_ledger_nodes": retained_ledger_nodes,
            "final_reachable_pair_nodes": reachable,
            "construction_counters": counters,
            "observation_counters": observation_counters,
            "warm_last_demand_counters": {
                key: value - before_warm.get(key, 0)
                for key, value in ledger.counters.items()
                if value != before_warm.get(key, 0)
            },
            "production_cutover_complete": False,
        }
    finally:
        grammar.close()
        if ledger.entries or ledger.nodes:
            raise AssertionError("spatial grammar probe leaked retained resources")


def research_event_measurement(seed: int, horizon: int) -> dict[str, object]:
    """Measure direct cylinder-event recovery, including temporal discovery.

    This finite research path is intentionally reported separately from both
    the pair-SLP prototype and the production cutover gate.
    """
    from devtools.experiments.reverse_add.centered_future import CenteredFutureGrammar
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.resources.ledger import ResourceLedger

    seed, horizon = _validated_measurement_inputs(seed, horizon)
    ledger = ResourceLedger()
    started = perf_counter()
    grammar = CenteredFutureGrammar(
        ledger, ExactSource(tuple(map(int, reversed(str(seed)))), 10, "reverse-add")
    )
    try:
        state = grammar.construct(horizon)
        construction_seconds = perf_counter() - started
        counters = dict(ledger.counters)
        nodes, entries, units = grammar.arena.node_count, ledger.entries, ledger.nodes
        started = perf_counter()
        runs = grammar.runs(state)
        observation_seconds = perf_counter() - started
        started = perf_counter()
        rendered = "".join(str(d) * (right - left) for left, right, d in reversed(runs))
        rendering_seconds = perf_counter() - started
        started = perf_counter()
        reference = seed
        for _ in range(horizon):
            reference += int(str(reference)[::-1])
        if rendered != str(reference):
            raise AssertionError("cylinder events disagree with bounded reference")
        reference_seconds = perf_counter() - started
        return {
            "scope": "research-cylinder-events-not-production",
            "seed": seed,
            "horizon": horizon,
            "cache_scope": "fresh-per-trial; no process cache used",
            "chronological_successors": counters.get(
                "reverse_centered_future_advances", 0
            ),
            "construction_seconds": construction_seconds,
            "observation_seconds": observation_seconds,
            "rendering_seconds": rendering_seconds,
            "reference_seconds": reference_seconds,
            "width": grammar.state(state).extent,
            "value": rendered,
            "retained_innovation_nodes": nodes,
            "retained_ledger_entries": entries,
            "retained_ledger_nodes": units,
            "construction_counters": counters,
            "production_cutover_complete": False,
        }
    finally:
        grammar.close()
        if ledger.entries or ledger.nodes:
            raise AssertionError("cylinder event probe leaked retained resources")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--order", choices=("ascending", "descending", "both"), default="both"
    )
    research = parser.add_mutually_exclusive_group()
    research.add_argument("--research-pair", action="store_true")
    research.add_argument("--research-events", action="store_true")
    parser.add_argument("--seed", type=int, default=196)
    parser.add_argument("--horizon", type=int, default=20)
    args = parser.parse_args(argv)
    result = (
        research_pair_measurement(args.seed, args.horizon)
        if args.research_pair
        else research_event_measurement(args.seed, args.horizon)
        if args.research_events
        else run_probe(args.order)
    )
    print(json.dumps(result, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
