"""Independent decimal-edge census and guarded finite macro differential audit."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

from devtools.paths import report_output
from devtools.verification.oracles.sequence_arithmetic import collatz_literal
from number_compiler.sequences.collatz.boundary_macros import (
    select_boundary_macro,
    validate_boundary_macro,
)


def decimal_cycles() -> tuple[set[tuple[int, int]], set[tuple[int, ...]]]:
    """Enumerate simple cycles of the exact twenty-residue physical graph."""
    edges = {
        (residue % 10, collatz_literal(20 + residue, 1) % 10) for residue in range(20)
    }
    successors: dict[int, list[int]] = {digit: [] for digit in range(10)}
    for source, target in sorted(edges):
        successors[source].append(target)
    cycles: set[tuple[int, ...]] = set()
    for start in range(10):
        pending: list[tuple[int, ...]] = [(start,)]
        while pending:
            path = pending.pop()
            for target in successors[path[-1]]:
                if target == start:
                    cycles.add(path)
                elif target > start and target not in path:
                    pending.append((*path, target))
    return edges, cycles


def audit(output: Path) -> dict[str, object]:
    edges, cycles = decimal_cycles()
    expected = {
        tuple(map(int, word))
        for word in ("0", "89", "142", "1472", "0563", "2684", "26847")
    }
    if len(edges) != 15 or cycles != expected:
        raise AssertionError(("unexpected decimal graph", edges, cycles))
    counts: Counter[str] = Counter()
    entries = (
        ("0563", 30, 40),
        ("26847", 112, 160),
        ("26847P1", 56, 80),
        ("26847P2", 28, 40),
        ("26847P3", 14, 20),
        ("26847P4", 7, 10),
    )
    for family, residue, modulus in entries:
        for offset in range(1600):
            source = residue + modulus * offset
            macro = select_boundary_macro(source, 128, minimum_repetitions=1)
            accepted = {family, "4721"} if family == "26847P3" else {family}
            if macro is None or macro.family not in accepted:
                raise AssertionError(("missing guarded macro", family, source))
            validate_boundary_macro(macro)
            if macro.endpoint != collatz_literal(source, macro.physical_ticks):
                raise AssertionError(("wrong physical endpoint", family, source))
            if macro.fields.endpoint(source) != macro.endpoint:
                raise AssertionError(("wrong affine endpoint", family, source))
            counts[family] += 1
    report: dict[str, object] = {
        "source_residue_guards": 20,
        "physical_digit_edges": len(edges),
        "elementary_digit_cycles": [
            "".join(map(str, cycle)) for cycle in sorted(cycles)
        ],
        "guarded_macro_fibers": dict(counts),
        "scope": "finite source-guarded prefixes, not Collatz convergence",
    }
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return report


def main() -> None:
    output = report_output(
        "devtools.experiments.collatz.nc11_edge_cycle_audit", "audit.json"
    )
    print(json.dumps(audit(output), sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
