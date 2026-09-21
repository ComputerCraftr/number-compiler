"""Cold schema-seven M(N, X) measurements with explicit horizon ordering."""

from __future__ import annotations

import argparse
import itertools
import json
from collections.abc import Callable, Iterable
from dataclasses import asdict, dataclass
from typing import Any


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
        if any(term._ledger is previous for previous in ledgers):
            raise AssertionError("cold probe constructor reused an index ledger")
        ledgers.append(term._ledger)
        digit = term.digit(0)
        metrics = term.metrics()
        if metrics.metrics_schema_version != 7 or metrics.forbidden_future_payloads:
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
        "metrics_schema_version": 7,
        "cold_index_scope": "fresh-per-row",
        "orders": results,
        "status": "GREEN" if green else ("RED" if complete else "unavailable"),
        "measurements_complete": complete,
        "logarithmic_execution_claim": False,
        "successor_closure_proved": False,
        "exact_bimachine_composition_available": True,
        "closure_field_scope": "legacy source-independent finite temporal quotient; not executor availability",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--order", choices=("ascending", "descending", "both"), default="both"
    )
    args = parser.parse_args(argv)
    print(json.dumps(run_probe(args.order), sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
