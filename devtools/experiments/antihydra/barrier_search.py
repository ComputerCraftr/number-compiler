"""Bounded source-aware refinement of spurious finite-residue barrier paths.

This experiment cannot turn a finite cylinder into an all-time certificate.
It reconstructs each abstract failure's exact entry cylinder and verifies the
lift by the canonical macro semantics before comparing it with source h=8.
"""

from __future__ import annotations

import argparse
import json
from collections import deque
from dataclasses import asdict
from time import perf_counter

from devtools.experiments.antihydra.event_domain import source_event_exponent_domain
from devtools.experiments.antihydra.future_grammar import ReachableFutureGrammar
from devtools.experiments.antihydra.source_safety import (
    SourceBlockID,
    SourceSafetyWorkspace,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.blocks import kernel
from number_compiler.sequences.antihydra.machine import MACHINE_SHA256


def candidate_failure(bits: int, depth: int, max_nodes: int) -> dict[str, object]:
    if not 1 <= bits <= 16 or not 1 <= depth <= 128 or max_nodes < 1:
        raise ValueError("invalid bounded refinement parameters")
    modulus = 1 << bits
    # residue, ledger, parent, chosen high bit, depth
    nodes = [(8 % modulus, 0, -1, 0, 0)]
    pending = deque([0])
    seen = {(8 % modulus, 0)}
    while pending:
        index = pending.popleft()
        residue, balance, _, _, steps = nodes[index]
        if steps == depth:
            continue
        for bit in (0, 1):
            target = ((3 * (residue + modulus * bit) - (residue & 1)) // 2) % modulus
            next_balance = balance + 2 - 3 * (residue & 1)
            if (target, next_balance) in seen:
                continue
            if len(nodes) == max_nodes:
                return {
                    "status": "BUDGET_EXHAUSTED",
                    "precision": bits,
                    "nodes": len(nodes),
                }
            seen.add((target, next_balance))
            nodes.append((target, next_balance, index, bit, steps + 1))
            child = len(nodes) - 1
            if next_balance >= 0:
                pending.append(child)
                continue
            path: list[int] = []
            cursor = child
            while nodes[cursor][2] >= 0:
                parent = nodes[cursor][2]
                path.append(nodes[parent][0] & 1)
                cursor = parent
            path.reverse()
            innovation = 0
            for i, parity in enumerate(path):
                innovation = 3 * innovation - parity * (1 << i)
            n = len(path)
            source_modulus = 1 << (bits + n)
            source_residue = (
                ((target << n) - innovation)
                * pow(3**n, -1, source_modulus)
                % source_modulus
            )
            witness = source_residue
            if witness < 8:
                witness += (
                    (8 - witness + source_modulus - 1) // source_modulus
                ) * source_modulus
            h, ledger = witness, 0
            for i, parity in enumerate(path):
                if h & 1 != parity:
                    raise ArithmeticError("abstract path has no claimed source lift")
                if i == n - 1:
                    if ledger != 0 or parity != 1:
                        raise ArithmeticError(
                            "claimed witness does not reach F0 section"
                        )
                else:
                    h, ledger, _, _ = kernel(parity, 1).apply(h, ledger)
            actual_source = (8 - source_residue) % source_modulus == 0
            return {
                "status": "SOURCE_COUNTEREXAMPLE"
                if actual_source
                else "SPURIOUS_SOURCE_PATH",
                "precision": bits,
                "nodes": len(nodes),
                "failure_depth": n,
                "parities": path,
                "entry_residue": source_residue,
                "entry_modulus": source_modulus,
                "other_source_witness": witness,
                "source_8_admitted": actual_source,
            }
    return {
        "status": "NO_FAILURE_WITHIN_BOUND",
        "precision": bits,
        "nodes": len(nodes),
        "depth_bound": depth,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=2)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--depth", type=int, default=32)
    parser.add_argument("--max-nodes", type=int, default=100000)
    parser.add_argument("--max-event", type=int, default=4)
    parser.add_argument(
        "--mode", choices=("ledger", "fractional", "grammar"), default="ledger"
    )
    args = parser.parse_args()
    if not 1 <= args.rounds <= 8:
        parser.error("rounds must be 1..8")
    if args.mode == "grammar":
        if not 1 <= args.max_event <= 64 or args.max_nodes < 1:
            parser.error("max-event must be 1..64 and max-nodes positive")
        print(
            json.dumps(
                grammar_refinement(args.rounds, args.max_event, args.max_nodes),
                sort_keys=True,
            )
        )
        return
    if args.mode == "fractional":
        print(
            json.dumps(
                fractional_refinement(args.rounds, args.max_nodes), sort_keys=True
            )
        )
        return
    records = []
    for bits in range(args.precision, args.precision + 2 * args.rounds, 2):
        record = candidate_failure(bits, args.depth, args.max_nodes)
        records.append(record)
        if record["status"] != "SPURIOUS_SOURCE_PATH":
            break
    print(
        json.dumps(
            {
                "machine_sha256": MACHINE_SHA256,
                "records": records,
                "nonhalting_certified": False,
                "certificate_synthesis_complete": False,
            },
            sort_keys=True,
        )
    )


def fractional_refinement(rounds: int, max_nodes: int) -> dict[str, object]:
    """Compose only admitted six-step source families, retaining symbolic k."""
    if not 1 <= rounds <= 8 or max_nodes < 1:
        raise ValueError("invalid bounded fractional refinement parameters")
    ledger = ResourceLedger(max_nodes=max_nodes, max_cache_entries=2 * max_nodes)
    workspace = SourceSafetyWorkspace(ledger, max_width=6 * rounds)
    records: list[dict[str, object]] = []
    status = "FINITE_PREFIXES_ONLY"
    try:
        bank = tuple(workspace.cylinder(6, r) for r in range(64))
        bank = tuple(
            handle for handle in bank if not workspace.view(handle).guard.empty
        )
        frontier: tuple[SourceBlockID, ...] = (workspace.cylinder(0, 0),)
        for stage in range(1, rounds + 1):
            start = perf_counter()
            survivors = []
            for first in frontier:
                for second in bank:
                    joint = workspace.compose(first, second)
                    if not workspace.view(joint).guard.empty:
                        survivors.append(joint)
            frontier = tuple(survivors)
            records.append(
                {
                    "horizon": 6 * stage,
                    "nonempty_cylinders": len(frontier),
                    "nodes": ledger.nodes,
                    "seconds": perf_counter() - start,
                }
            )
    except BlockContextBudgetExceeded:
        status = "BUDGET_EXHAUSTED"
    return {
        "predicate": "original_real_fractional_safety",
        "status": status,
        "records": records,
        "symbolic_high_fiber": "all natural k",
        "work": dict(ledger.counters),
        "retained_nodes": ledger.nodes,
        "nonhalting_certified": False,
        "global_safety_decided": False,
    }


def grammar_refinement(
    rounds: int, max_event: int, max_nodes: int
) -> dict[str, object]:
    """Search finite reachable clauses and challenge their fractional cycles.

    Observer samples are explicitly finite witnesses, not abstract-state merges.
    Larger event exponents remain unexplored, including after a successful run.
    """
    if not 1 <= rounds <= 8 or not 1 <= max_event <= 64 or max_nodes < 1:
        raise ValueError("invalid reachable grammar bounds")
    ledger = ResourceLedger(max_nodes=max_nodes, max_cache_entries=4 * max_nodes)
    records: list[dict[str, object]] = []
    observations: list[dict[str, object]] = []
    cycles: list[dict[str, object]] = []
    status = "FINITE_REACHABLE_GRAMMAR"
    try:
        workspace = SourceSafetyWorkspace(ledger, max_width=rounds * max_event)
        grammar = ReachableFutureGrammar(workspace, max_event=max_event)
        frontier: tuple[SourceBlockID, ...] = (grammar.root,)
        for depth in range(1, rounds + 1):
            start = perf_counter()
            survivors = []
            cycle_count = 0
            empty_count = 0
            for parent in frontier:
                domain = source_event_exponent_domain(workspace, parent)
                first = max_event + 1 if domain.first is None else domain.first
                last = max_event if domain.last is None else min(max_event, domain.last)
                admitted_count = max(0, last - first + 1)
                pruned = max_event - admitted_count
                empty_count += pruned
                ledger.bump("grammar_event_branches_pruned", pruned)
                for exponent in range(first, last + 1):
                    child = grammar.extend(parent, exponent)
                    block = workspace.view(child)
                    if block.guard.empty:
                        raise ArithmeticError(
                            "event domain admitted an empty source guard"
                        )
                    survivors.append(child)
                    source, _ = grammar.witness(child)
                    obstruction = grammar.periodic_obstruction(child, source)
                    if obstruction.fractional_cycle_admitted:
                        cycle_count += 1
                        if len(cycles) < 4:
                            cycles.append(
                                {
                                    "width": block.width,
                                    "residue": block.residue,
                                    "guard": asdict(block.guard),
                                    "telescoping": asdict(grammar.telescoping(child)),
                                    "obstruction": asdict(obstruction),
                                }
                            )
                            observation = grammar.observe_edge(parent, exponent)
                            row = asdict(observation)
                            row["readouts"]["subtraction"] = tuple(
                                fn.value for fn in observation.readouts.subtraction
                            )
                            observations.append(row)
            frontier = tuple(survivors)
            records.append(
                {
                    "event_depth": depth,
                    "reachable_families": len(frontier),
                    "empty_chronological_guards": empty_count,
                    "fractional_cycles_with_source_obstruction": cycle_count,
                    "seconds": perf_counter() - start,
                }
            )
    except BlockContextBudgetExceeded:
        status = "BUDGET_EXHAUSTED"
    return {
        "status": status,
        "records": records,
        "sample_periodic_obligations": cycles,
        "joint_finite_witness_observations": observations,
        "event_exploration_bound": max_event,
        "larger_event_branches": "UNEXPLORED",
        "high_fibers": "symbolic natural parameters constrained by each full prefix",
        "observer_samples": "one dyadic witness per sampled finite family; not a common infinite source",
        "all_time_quotient_certified": False,
        "global_safety_decided": False,
        "nonhalting_certified": False,
        "work": dict(ledger.counters),
        "retained_nodes": ledger.nodes,
        "retained_entries": ledger.entries,
    }


if __name__ == "__main__":
    main()
