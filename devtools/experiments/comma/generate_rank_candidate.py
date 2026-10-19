"""Generate an *untrusted* Isabelle rank candidate for the comma quotient.

The output is data only.  Isabelle must independently evaluate its own
finite transition, prove every boundary macro is complete, and check the
candidate against every actual quotient child.  This script is deliberately
absent from the installed package and is never an admission oracle.
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Iterator
from dataclasses import dataclass
from itertools import zip_longest
from pathlib import Path
from typing import Literal, TypedDict

from devtools.paths import isabelle_root
from number_compiler.sequences.comma.arithmetic import (
    cycle_power_residue,
    cycle_transfer,
)
from number_compiler.sequences.comma.boundary_chart import (
    MAX_CHART_MOVES,
    PERIOD,
    BoundaryChart,
    ChartMove,
    chart_moves,
    chart_step,
    initial_chart,
)

STATE_COUNT = 16 * PERIOD
PADDED_COUNT = 16_384
DEFAULT_OUTPUT = (
    isabelle_root() / "families/comma/comma_future_rank_data/Comma_Rank_Data.thy"
)
CONTROL_WITNESS_SCHEMA = 1
DECADE_RANK_SCHEMA = 1
DECADE_OFFSETS = 91
ROUND_MEASURE_RADIX = 1024


class ControlWitness(TypedDict):
    source: dict[str, object]
    start: list[int | str]
    positions: list[list[int | str]]
    outcome: dict[str, int | str]
    depth: int
    phase_normalization: list[dict[str, int]]


@dataclass(frozen=True, slots=True)
class RoundClosure:
    kind: Literal["continue", "fork", "landmine"]
    positions: int
    terminal_chart: BoundaryChart
    successor_chart: BoundaryChart | None
    fork_a: int | None


@dataclass(frozen=True, slots=True)
class DecadeRoundCandidate:
    """Untrusted derived round outcome; only ``chart_step`` decides moves."""

    phase: int
    offset: int
    kind: Literal["continue", "fork", "landmine"]
    positions: int
    terminal_chart: BoundaryChart
    successor: tuple[int, int] | None
    fork_a: int | None


def _round_measure(chart: BoundaryChart) -> int:
    if chart.kind == "entry":
        return (9 - chart.leading) * ROUND_MEASURE_RADIX + 600
    return (9 - chart.leading) * ROUND_MEASURE_RADIX + chart.coordinate


def _round_close_candidate(residue: int, start: BoundaryChart) -> RoundClosure:
    """Follow canonical chart moves through one decimal exponent shift.

    This is a candidate computation, not a proof of the rank or a runtime
    admission path. Every same-decimal transition must lower the displayed
    well-founded measure; the 9-to-1 crossing ends the round.
    """
    if not 0 <= residue < PERIOD:
        raise ValueError("invalid decimal-round residue")
    chart = start
    positions = 0
    while True:
        positions += 1
        move = chart_step(residue, chart)
        next_chart = move.next_chart
        if next_chart is None:
            if move.terminal_chart != chart:
                raise AssertionError("round terminal is not source-bound")
            return RoundClosure(
                "fork" if move.fork_a is not None else "landmine",
                positions,
                chart,
                None,
                move.fork_a,
            )
        if next_chart.delta != chart.delta:
            if not (
                chart.kind == "near"
                and chart.leading == 9
                and next_chart.kind == "entry"
                and next_chart.leading == 1
                and next_chart.delta == chart.delta + 1
                and 0 <= next_chart.coordinate < DECADE_OFFSETS
            ):
                raise AssertionError("round crossed an unproved decimal seam")
            return RoundClosure(
                "continue",
                positions,
                chart,
                next_chart,
                None,
            )
        if not _round_measure(next_chart) < _round_measure(chart):
            raise AssertionError("decimal-round measure failed to decrease")
        chart = next_chart


def decade_round_candidate(phase: int, offset: int) -> DecadeRoundCandidate:
    if not 0 <= phase < PERIOD or not 0 <= offset < DECADE_OFFSETS:
        raise ValueError("invalid decimal-round state")
    closure = _round_close_candidate(phase, BoundaryChart("entry", 1, 0, offset))
    return _decade_from_closure(phase, offset, closure)


def _decade_from_closure(
    phase: int, offset: int, closure: RoundClosure
) -> DecadeRoundCandidate:
    successor = closure.successor_chart
    return DecadeRoundCandidate(
        phase,
        offset,
        closure.kind,
        closure.positions,
        closure.terminal_chart,
        ((phase + successor.delta) % PERIOD, successor.coordinate)
        if successor is not None
        else None,
        closure.fork_a,
    )


def boundary_partial_round_candidate(
    kind: Literal["N", "Z"], a: int, residue: int
) -> tuple[RoundClosure, tuple[int, int] | None]:
    """Map an admitted boundary source to its first derived decade state."""
    closure = _round_close_candidate(residue, initial_chart(kind, a))
    successor = closure.successor_chart
    if successor is None:
        return closure, None
    return closure, ((residue + successor.delta) % PERIOD, successor.coordinate)


def _decade_round_graph() -> list[DecadeRoundCandidate]:
    return [
        decade_round_candidate(phase, offset)
        for phase in range(PERIOD)
        for offset in range(DECADE_OFFSETS)
    ]


def phase_factorization_profile() -> tuple[dict[int, int], int]:
    """Measure reusable canonical Entry germs, without adding a transition rule.

    For each of the 17 admitted displacements, infer its least period from
    ``cycle_power_residue``. A normalized Entry germ is then indexed by
    ``(leading, offset, phase mod short_period(displacement))``. The returned
    count is only research evidence for a proof-producing HOL memo strategy.
    """
    catalog = sorted(
        {
            cycle_transfer(f, digit).displacement
            for f in range(1, 10)
            for digit in range(10)
        }
    )
    periods: dict[int, int] = {}
    for displacement in catalog:
        values = [cycle_power_residue(displacement, r) for r in range(PERIOD)]
        periods[displacement] = next(
            step
            for step in range(1, PERIOD + 1)
            if PERIOD % step == 0
            and all(values[r] == values[(r + step) % PERIOD] for r in range(PERIOD))
        )
    entry_cases = sum(
        periods[cycle_transfer(f, offset % 10).displacement]
        for f in range(1, 10)
        for offset in range(DECADE_OFFSETS)
    )
    return periods, entry_cases


def _decade_rank_candidates(graph: list[DecadeRoundCandidate]) -> list[int]:
    """Compute untrusted internal-constructor ranks, separate from boundary safety."""
    if len(graph) != PERIOD * DECADE_OFFSETS:
        raise ValueError("incomplete decimal-round graph")
    ranks = [-1] * len(graph)
    for root in range(len(graph)):
        if ranks[root] >= 0:
            continue
        path: list[int] = []
        seen: set[int] = set()
        current = root
        while ranks[current] < 0:
            if current in seen:
                raise AssertionError(f"cycle in decimal-round candidate at {current}")
            seen.add(current)
            path.append(current)
            successor = graph[current].successor
            if successor is None:
                break
            current = successor[0] * DECADE_OFFSETS + successor[1]
        while path:
            index = path.pop()
            successor = graph[index].successor
            ranks[index] = (
                0
                if successor is None
                else 1 + ranks[successor[0] * DECADE_OFFSETS + successor[1]]
            )
    return ranks


def _decade_rank_lines(
    graph: list[DecadeRoundCandidate], ranks: list[int]
) -> Iterator[str]:
    if len(graph) != PERIOD * DECADE_OFFSETS or len(ranks) != len(graph):
        raise ValueError("incomplete decimal-round candidate")
    for index, candidate in enumerate(graph):
        successor = candidate.successor
        expected = (
            0
            if successor is None
            else 1 + ranks[successor[0] * DECADE_OFFSETS + successor[1]]
        )
        if ranks[index] != expected:
            raise AssertionError("decimal-round rank disagrees with canonical edge")
    max_rank = max(ranks)
    first_max = ranks.index(max_rank)
    first_max_chain: list[tuple[int, int]] = []
    current = first_max
    while True:
        candidate = graph[current]
        first_max_chain.append((candidate.phase, candidate.offset))
        successor = candidate.successor
        if successor is None:
            break
        current = successor[0] * DECADE_OFFSETS + successor[1]
    if len(first_max_chain) != max_rank + 1:
        raise AssertionError("decimal-round max-rank chain has wrong length")
    yield (
        json.dumps(
            {
                "schema": DECADE_RANK_SCHEMA,
                "candidate_only": True,
                "states": len(graph),
                "measure_radix": ROUND_MEASURE_RADIX,
                "rank_meaning": "continuing_round_edges_not_boundary_safety",
                "terminal_rank": 0,
                "max_rank": max_rank,
                "max_round_evaluations": max_rank + 1,
                "first_max_source": first_max_chain[0],
                "first_max_chain": first_max_chain,
            },
            separators=(",", ":"),
            sort_keys=True,
        )
        + "\n"
    )
    for phase in range(PERIOD):
        start = phase * DECADE_OFFSETS
        yield (
            json.dumps(
                {
                    "phase": phase,
                    "ranks": ranks[start : start + DECADE_OFFSETS],
                },
                separators=(",", ":"),
                sort_keys=True,
            )
            + "\n"
        )


def _write_decade_rank(path: Path, *, check: bool) -> None:
    graph = _decade_round_graph()
    ranks = _decade_rank_candidates(graph)
    lines = _decade_rank_lines(graph, ranks)
    if check:
        with path.open(encoding="utf-8") as existing:
            for expected, actual in zip_longest(lines, existing):
                if expected != actual:
                    raise SystemExit(f"decimal-round candidate differs: {path}")
    else:
        with path.open("w", encoding="utf-8") as output:
            output.writelines(lines)
    print(path)


def _isabelle_chart(chart: BoundaryChart) -> str:
    constructor = "Comma_Entry" if chart.kind == "entry" else "Comma_Near"
    return f"{constructor} {chart.leading} {chart.delta} {chart.coordinate}"


def _round_phase_lines(phase: int) -> Iterator[str]:
    """Emit untrusted outcomes only; the ML checker independently proves them."""
    if not 0 <= phase < PERIOD:
        raise ValueError("round phase must lie in 0..923")
    yield "(* Generated by generate_rank_candidate.py --round-phase-only.\n"
    yield "   Candidate equations are data, never transition assumptions. *)\n"
    yield f"val comma_round_candidate_phase = {phase};\n"
    yield "val comma_round_phase_candidates = [\n"
    for offset in range(DECADE_OFFSETS):
        closure = _round_close_candidate(phase, BoundaryChart("entry", 1, 0, offset))
        if closure.kind == "continue":
            target = closure.successor_chart
            if target is None:
                raise AssertionError("cross witness lacks its target")
            outcome = f"Comma_Round_Cross ({_isabelle_chart(target)})"
        elif closure.kind == "fork":
            outcome = (
                f"Comma_Round_Fork {closure.fork_a} {closure.terminal_chart.delta}"
            )
        else:
            outcome = f"Comma_Round_Landmine {closure.terminal_chart.delta}"
        comma = "," if offset + 1 < DECADE_OFFSETS else ""
        yield (
            f'  @{{prop "comma_round_close {phase} (Comma_Entry 1 0 {offset}) = '
            f"({closure.positions - 1}, {_isabelle_chart(closure.terminal_chart)}, "
            f'{outcome})"}}{comma}\n'
        )
    yield "];\n"


def _write_round_phase(path: Path, phase: int, *, check: bool) -> None:
    lines = _round_phase_lines(phase)
    if check:
        with path.open(encoding="utf-8") as existing:
            for expected, actual in zip_longest(lines, existing):
                if expected != actual:
                    raise SystemExit(f"round phase candidate differs: {path}")
    else:
        with path.open("w", encoding="utf-8") as output:
            output.writelines(lines)
    print(path)


def _chart_data(chart: BoundaryChart) -> list[int | str]:
    return [chart.kind, chart.leading, chart.delta, chart.coordinate]


def _assemble_control_witness(
    source: dict[str, object],
    start: BoundaryChart,
    residue: int,
    moves: Iterator[tuple[BoundaryChart, ChartMove]],
) -> ControlWitness:
    positions: list[list[int | str]] = []
    terminal: dict[str, int | str] | None = None
    for chart, move in moves:
        positions.append(_chart_data(chart))
        if move.next_chart is not None:
            if move.terminal_chart is not None or move.fork_a is not None:
                raise AssertionError("nonterminal chart carries a terminal label")
            continue
        if move.terminal_chart != chart:
            raise AssertionError("canonical terminal chart differs from source")
        if move.fork_a is not None:
            terminal = {"kind": "fork", "a": move.fork_a, "delta": chart.delta}
        else:
            terminal = {"kind": "landmine", "delta": chart.delta}
    if not positions or terminal is None:
        raise AssertionError("canonical chart did not terminate")
    if positions[0] != _chart_data(start):
        raise AssertionError("canonical chart changed its initial position")
    deltas = sorted({int(position[2]) for position in positions})
    return {
        "source": source,
        "start": positions[0],
        "positions": positions,
        "outcome": terminal,
        "depth": len(positions),
        "phase_normalization": [
            {"delta": delta, "residue": (residue + delta) % PERIOD} for delta in deltas
        ],
    }


def _control_witness(kind: Literal["N", "Z"], a: int, residue: int) -> ControlWitness:
    """Construct an untrusted boundary witness from the canonical chart.

    Isabelle must independently check every position and terminal outcome.
    This candidate grants no branch or totality authority.
    """
    start = initial_chart(kind, a)
    return _assemble_control_witness(
        {"kind": kind, "a": a, "residue": residue},
        start,
        residue,
        chart_moves(kind, a, residue),
    )


def _chart_moves_from(
    start: BoundaryChart, residue: int
) -> Iterator[tuple[BoundaryChart, ChartMove]]:
    """Use the same local step to propose a trace from a non-boundary chart."""
    chart = start
    for _ in range(MAX_CHART_MOVES):
        move = chart_step(residue, chart)
        yield chart, move
        if move.next_chart is None:
            return
        chart = move.next_chart
    raise ValueError("comma chart exceeded its finite seam bound")


def control_witness_from_chart(start: BoundaryChart, residue: int) -> ControlWitness:
    """Propose a control witness for a caller-supplied intermediate chart."""
    return _assemble_control_witness(
        {"chart": _chart_data(start), "residue": residue},
        start,
        residue,
        _chart_moves_from(start, residue),
    )


def _witness_slices(
    kind: Literal["N", "Z"] | None, a: int | None
) -> list[tuple[Literal["N", "Z"], int]]:
    if a is not None and not 2 <= a <= 9:
        raise ValueError("boundary a must lie in 2..9")
    kinds: tuple[Literal["N", "Z"], ...] = (kind,) if kind else ("N", "Z")
    digits: tuple[int, ...] | range = (a,) if a is not None else range(2, 10)
    return [(side, digit) for side in kinds for digit in digits]


def _witness_slice_lines(kind: Literal["N", "Z"], a: int) -> Iterator[str]:
    header = {
        "schema": CONTROL_WITNESS_SCHEMA,
        "candidate_only": True,
        "kind": kind,
        "a": a,
        "period": PERIOD,
    }
    yield json.dumps(header, separators=(",", ":"), sort_keys=True) + "\n"
    for residue in range(PERIOD):
        yield (
            json.dumps(
                _control_witness(kind, a, residue),
                separators=(",", ":"),
                sort_keys=True,
            )
            + "\n"
        )


def _write_witness_slices(
    directory: Path,
    *,
    kind: Literal["N", "Z"] | None,
    a: int | None,
    check: bool,
) -> None:
    if not check:
        directory.mkdir(parents=True, exist_ok=True)
    for side, digit in _witness_slices(kind, a):
        path = directory / f"comma-control-{side}-{digit}.jsonl"
        if check:
            with path.open(encoding="utf-8") as existing:
                for expected, actual in zip_longest(
                    _witness_slice_lines(side, digit), existing
                ):
                    if expected != actual:
                        raise SystemExit(
                            f"comma control witness candidate differs: {path}"
                        )
        else:
            with path.open("w", encoding="utf-8") as output:
                output.writelines(_witness_slice_lines(side, digit))
        print(path)


def _macro_children(index: int) -> tuple[int, ...]:
    if not 0 <= index < STATE_COUNT:
        raise ValueError("boundary quotient index outside finite type")
    side, remainder = divmod(index, 8 * PERIOD)
    ordinal, source_residue = divmod(remainder, PERIOD)
    for chart, move in chart_moves(
        "N" if side == 0 else "Z", ordinal + 2, source_residue
    ):
        if move.next_chart is None:
            if move.fork_a is None:
                return ()
            child_residue = (source_residue + chart.delta) % PERIOD
            near = (move.fork_a - 2) * PERIOD + child_residue
            return near, near + 8 * PERIOD
    raise AssertionError("comma chart returned without an outcome")


def _candidate_ranks() -> list[int]:
    graph = [_macro_children(index) for index in range(STATE_COUNT)]
    rank = {index: 0 for index, children in enumerate(graph) if not children}
    while True:
        found = {
            index: 1 + max(rank[child] for child in children)
            for index, children in enumerate(graph)
            if index not in rank
            and children
            and all(child in rank for child in children)
        }
        if not found:
            break
        rank.update(found)
    codes = [rank[index] + 1 if index in rank else 0 for index in range(STATE_COUNT)]
    codes.extend([0] * (PADDED_COUNT - STATE_COUNT))
    return codes


def _render_rank_side(kind: Literal["N", "Z"], codes: list[int]) -> str:
    """Render one semantic boundary side, using the canonical radix-16 tree."""
    if len(codes) != PADDED_COUNT:
        raise ValueError("invalid candidate length")
    start = 0 if kind == "N" else 8 * PERIOD
    values = codes[start : start + 8 * PERIOD]
    values.extend([0] * (PADDED_COUNT // 2 - len(values)))
    name = f"comma_rank_codes_{kind}"
    parts = [
        f"theory Comma_Rank_Data_{kind}\n",
        "  imports Comma_Arithmetic.Comma_Boundary_Primitives\nbegin\n\n",
        f"text \\<open>Untrusted rank codes for all {kind} boundary states, ordered\n",
        "by leading coefficient then phase. Zero denotes an unranked candidate;\n",
        "positive codes encode rank plus one. Padding is outside the catalog.\n",
        "These definitions confer no branch authority.\\<close>\n\n",
        f'definition {name} :: "nat list list list list" where\n',
        f'  "{name} = [\n',
    ]
    for top in range(2):
        parts.append("    [\n")
        for second in range(16):
            parts.append("      [\n")
            for third in range(16):
                offset = ((top * 16 + second) * 16 + third) * 16
                leaf = values[offset : offset + 16]
                parts.append(
                    "        ["
                    + ", ".join(map(str, leaf))
                    + "]"
                    + ("," if third < 15 else "")
                    + "\n"
                )
            parts.append("      ]" + ("," if second < 15 else "") + "\n")
        parts.append("    ]" + ("," if top < 1 else "") + "\n")
    parts.extend(
        [
            '  ]"\n\n',
            "ML \\<open>\n",
            f"  val _ = if null (Thm_Deps.all_oracles @{{thms {name}_def}})\n",
            f'    then () else error "Comma {kind} rank data depends on an oracle";\n',
            "\\<close>\n\nend\n",
        ]
    )
    return "".join(parts)


def _rank_candidate_files(output: Path, codes: list[int]) -> dict[Path, str]:
    # Lookup and admission are authored proofs, never regenerated from data.
    return {
        output.with_name("Comma_Rank_Data_N.thy"): _render_rank_side("N", codes),
        output.with_name("Comma_Rank_Data_Z.thy"): _render_rank_side("Z", codes),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="lookup owner path; generate only sibling N/Z candidate data theories",
    )
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--witness-dir",
        type=Path,
        help="also write untrusted control-position JSONL, one file per kind/a slice",
    )
    parser.add_argument("--witness-kind", choices=("N", "Z"))
    parser.add_argument("--witness-a", type=int)
    parser.add_argument(
        "--witness-only",
        action="store_true",
        help="generate selected control witnesses without building rank data",
    )
    parser.add_argument(
        "--decade-rank-output",
        type=Path,
        help="stream untrusted 924-by-91 internal decimal-round ranks as JSONL",
    )
    parser.add_argument(
        "--decade-rank-only",
        action="store_true",
        help="generate decimal-round ranks without boundary rank data",
    )
    parser.add_argument("--round-phase-output", type=Path)
    parser.add_argument("--round-phase", type=int, default=5)
    parser.add_argument(
        "--round-phase-only",
        action="store_true",
        help="generate one untrusted 91-offset round slice without rank data",
    )
    args = parser.parse_args()
    if args.round_phase_only and args.round_phase_output is None:
        parser.error("--round-phase-only requires --round-phase-output")
    if not 0 <= args.round_phase < PERIOD:
        parser.error("--round-phase must lie in 0..923")
    if args.witness_only and args.witness_dir is None:
        parser.error("--witness-only requires --witness-dir")
    if (args.witness_kind is not None or args.witness_a is not None) and (
        args.witness_dir is None
    ):
        parser.error("--witness-kind and --witness-a require --witness-dir")
    if args.witness_a is not None and not 2 <= args.witness_a <= 9:
        parser.error("--witness-a must lie in 2..9")
    if args.decade_rank_only and args.decade_rank_output is None:
        parser.error("--decade-rank-only requires --decade-rank-output")
    if not (args.witness_only or args.decade_rank_only or args.round_phase_only):
        files = _rank_candidate_files(args.output, _candidate_ranks())
        for path, content in files.items():
            if args.check:
                if path.read_text() != content:
                    raise SystemExit(f"comma rank candidate differs: {path}")
            else:
                path.write_text(content)
                print(path)
        if args.check:
            print("comma rank candidate matches deterministic generator")
    if args.witness_dir is not None:
        _write_witness_slices(
            args.witness_dir,
            kind=args.witness_kind,
            a=args.witness_a,
            check=args.check,
        )
    if args.decade_rank_output is not None:
        _write_decade_rank(args.decade_rank_output, check=args.check)
    if args.round_phase_output is not None:
        _write_round_phase(args.round_phase_output, args.round_phase, check=args.check)


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
