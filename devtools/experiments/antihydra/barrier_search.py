"""Bounded source-aware refinement of spurious finite-residue barrier paths.

This experiment cannot turn a finite cylinder into an all-time certificate.
It reconstructs each abstract failure's exact entry cylinder and verifies the
lift by the canonical macro semantics before comparing it with source h=8.
"""

from __future__ import annotations

import argparse
import json
from collections import deque

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
            target = ((3*(residue+modulus*bit)-(residue & 1))//2) % modulus
            next_balance = balance+2-3*(residue & 1)
            if (target, next_balance) in seen:
                continue
            if len(nodes) == max_nodes:
                return {"status": "BUDGET_EXHAUSTED", "precision": bits, "nodes": len(nodes)}
            seen.add((target, next_balance))
            nodes.append((target, next_balance, index, bit, steps+1))
            child = len(nodes)-1
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
                innovation = 3*innovation-parity*(1 << i)
            n = len(path)
            source_modulus = 1 << (bits+n)
            source_residue = ((target << n)-innovation)*pow(3**n, -1, source_modulus) % source_modulus
            witness = source_residue
            if witness < 8:
                witness += ((8-witness+source_modulus-1)//source_modulus)*source_modulus
            h, ledger = witness, 0
            for i, parity in enumerate(path):
                if h & 1 != parity:
                    raise ArithmeticError("abstract path has no claimed source lift")
                if i == n-1:
                    if ledger != 0 or parity != 1:
                        raise ArithmeticError("claimed witness does not reach F0 section")
                else:
                    h, ledger, _, _ = kernel(parity, 1).apply(h, ledger)
            actual_source = (8-source_residue) % source_modulus == 0
            return {"status": "SOURCE_COUNTEREXAMPLE" if actual_source else "SPURIOUS_SOURCE_PATH",
                    "precision": bits, "nodes": len(nodes), "failure_depth": n,
                    "parities": path, "entry_residue": source_residue,
                    "entry_modulus": source_modulus, "other_source_witness": witness,
                    "source_8_admitted": actual_source}
    return {"status": "NO_FAILURE_WITHIN_BOUND", "precision": bits, "nodes": len(nodes),
            "depth_bound": depth}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=2)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--depth", type=int, default=32)
    parser.add_argument("--max-nodes", type=int, default=100000)
    args = parser.parse_args()
    if not 1 <= args.rounds <= 8:
        parser.error("rounds must be 1..8")
    records = []
    for bits in range(args.precision, args.precision+2*args.rounds, 2):
        record = candidate_failure(bits, args.depth, args.max_nodes)
        records.append(record)
        if record["status"] != "SPURIOUS_SOURCE_PATH":
            break
    print(json.dumps({"machine_sha256": MACHINE_SHA256, "records": records,
                      "nonhalting_certified": False, "certificate_synthesis_complete": False}, sort_keys=True))


if __name__ == "__main__":
    main()
