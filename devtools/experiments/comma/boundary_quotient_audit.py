"""Independent finite audit of the proposed comma boundary quotient.

This is development tooling.  It is deliberately absent from the installed
sequence route, and its results cannot substitute for a lifting proof.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Literal

from devtools.benchmarks.report_schema import sequence
from devtools.experiments.comma.macro_lifting import check_macro_lifting
from number_compiler.arithmetic.contracts.input_validation import (
    is_object_list,
    string_keyed_mapping,
)
from number_compiler.sequences.comma.boundary_quotient import (
    PERIOD,
    BoundaryState,
    construct_macro,
)
from number_compiler.sequences.comma.weighted_return import WeightedBoundaryAction

TOTAL_STATES = 16 * PERIOD


def boundary_state(index: object) -> BoundaryState:
    if type(index) is not int or not 0 <= index < TOTAL_STATES:
        raise ValueError("boundary quotient index outside finite type")
    side, rest = divmod(index, 8 * PERIOD)
    leading, residue = divmod(rest, PERIOD)
    kind: Literal["N", "Z"] = "N" if side == 0 else "Z"
    return BoundaryState(kind, leading + 2, residue)


def state_index(state: BoundaryState) -> int:
    return (int(state.kind == "Z") * 8 + state.a - 2) * PERIOD + state.exponent_residue


def generate_shard(start: int, stop: int) -> dict[str, object]:
    if (
        type(start) is not int
        or type(stop) is not int
        or not 0 <= start < stop <= TOTAL_STATES
    ):
        raise ValueError("invalid comma quotient shard")
    rows: list[list[object]] = []
    for index in range(start, stop):
        macro = construct_macro(boundary_state(index))
        checked_fragments = check_macro_lifting(macro)
        rows.append(
            [
                index,
                [state_index(child) for child in macro.ordered_children],
                macro.exponent_delta,
                checked_fragments,
            ]
        )
    return {"schema": 1, "start": start, "stop": stop, "rows": rows}


def summarize_shards(
    paths: list[Path], *, weighted_return: bool = False
) -> dict[str, object]:
    graph: dict[BoundaryState, tuple[BoundaryState, ...]] = {}
    exponent_gain: dict[BoundaryState, int] = {}
    max_fragments = 0
    for path in paths:
        raw_packet: object = json.loads(path.read_text())
        packet = string_keyed_mapping(raw_packet)
        if packet is None:
            raise ValueError("unsupported comma audit shard schema")
        if (
            set(packet) != {"schema", "start", "stop", "rows"}
            or type(packet["schema"]) is not int
            or packet["schema"] != 1
        ):
            raise ValueError("unsupported comma audit shard schema")
        start, stop = packet["start"], packet["stop"]
        if (
            type(start) is not int
            or type(stop) is not int
            or not 0 <= start < stop <= TOTAL_STATES
        ):
            raise ValueError("invalid comma audit shard bounds")
        rows = packet["rows"]
        if not is_object_list(rows) or len(rows) != stop - start:
            raise ValueError("truncated comma audit shard")
        for expected, row in enumerate(sequence(rows), start):
            if not is_object_list(row) or len(row) != 4:
                raise ValueError("invalid comma audit row")
            index, children, gain, fragments = sequence(row)
            if type(index) is not int or index != expected:
                raise ValueError("unordered comma audit shard")
            if (
                type(gain) is not int
                or gain < 0
                or type(fragments) is not int
                or fragments <= 0
            ):
                raise ValueError("invalid comma audit construction counts")
            if not is_object_list(children) or len(children) not in (0, 2):
                raise ValueError("incomplete comma fork alternatives")
            state = boundary_state(index)
            alternatives = tuple(boundary_state(child) for child in children)
            if alternatives:
                left, right = alternatives
                if (
                    left.kind != "N"
                    or right.kind != "Z"
                    or left.a != right.a
                    or left.exponent_residue != right.exponent_residue
                    or left.exponent_residue != (state.exponent_residue + gain) % PERIOD
                ):
                    raise ValueError("unbound comma fork alternatives")
            if state in graph:
                raise ValueError("duplicate comma quotient state")
            graph[state] = alternatives
            exponent_gain[state] = gain
            max_fragments = max(max_fragments, fragments)
    if len(graph) != TOTAL_STATES:
        raise ValueError("incomplete comma quotient audit")
    states = tuple(boundary_state(index) for index in range(TOTAL_STATES))

    rank: dict[BoundaryState, int] = {
        state: 0 for state, children in graph.items() if not children
    }
    while True:
        newly = {
            state: 1 + max(rank[child] for child in children)
            for state, children in graph.items()
            if state not in rank
            and children
            and all(child in rank for child in children)
        }
        if not newly:
            break
        rank.update(newly)

    winning = set(states) - rank.keys()
    if any(sum(child in winning for child in graph[state]) != 1 for state in winning):
        raise AssertionError("winning quotient is not a unique-successor graph")
    first = BoundaryState("N", 2, 10)
    if first not in winning:
        raise AssertionError("the known first-fork branch is losing")
    visited: dict[BoundaryState, int] = {}
    cursor = first
    elapsed_exponents = 0
    choices: list[int] = []
    while cursor not in visited:
        visited[cursor] = len(visited)
        children = graph[cursor]
        successor = next(child for child in children if child in winning)
        choices.append(children.index(successor))
        elapsed_exponents += exponent_gain[cursor]
        cursor = successor
    if cursor != first or len(visited) != len(winning):
        raise AssertionError("winning quotient is not the one root cycle")
    result: dict[str, object] = {
        "states": len(states),
        "losing": len(rank),
        "winning": len(winning),
        "rank_max": max(rank.values()),
        "cycle_forks": len(visited),
        "cycle_exponent_gain": elapsed_exponents,
        "cycle_choice_prefix": "".join(str(v) for v in choices[:40]),
        "outcomes": dict(Counter(len(children) for children in graph.values())),
        "maximum_sector_fragments": max_fragments,
    }
    if weighted_return:
        action = WeightedBoundaryAction.identity(first)
        work = bit_work = 0

        def charge(amount: int) -> None:
            nonlocal work
            work += amount

        def charge_bits(amount: int) -> None:
            nonlocal bit_work
            bit_work += amount

        # Reconstruct and recheck each macro: shard summaries do not contain
        # enough information to authorize a weighted return or partial demand.
        for state, choice in zip(visited, choices, strict=True):
            macro = construct_macro(state, charge=charge, charge_bits=charge_bits)
            check_macro_lifting(macro)
            if (
                macro.ordered_children != graph[state]
                or macro.exponent_delta != exponent_gain[state]
            ):
                raise ValueError("weighted return disagrees with quotient shard")
            edge = WeightedBoundaryAction.from_selected_fork(
                macro, macro.ordered_children[choice]
            )
            action = action.then(edge, charge=charge, charge_bits=charge_bits)
        if action.end != first or action.exponent_delta != elapsed_exponents:
            raise AssertionError("weighted return did not close the boundary cycle")
        weight = action.weight
        result["weighted_return"] = {
            "numerator_scale": str(weight.numerator_scale),
            "numerator_offset": str(weight.numerator_offset),
            "denominator": str(weight.denominator),
            "exponent_gain": action.exponent_delta,
            "constructor_composition_operations": work,
            "constructor_composition_operand_bit_work": bit_work,
            "checker_work_included": False,
            "production_admission": False,
        }
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int, default=TOTAL_STATES)
    parser.add_argument("--merge", type=Path, nargs="+")
    parser.add_argument("--weighted-return", action="store_true")
    args = parser.parse_args()
    if args.weighted_return and not args.merge:
        parser.error("--weighted-return requires --merge")
    result = (
        summarize_shards(args.merge, weighted_return=args.weighted_return)
        if args.merge
        else generate_shard(args.start, args.stop)
    )
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
