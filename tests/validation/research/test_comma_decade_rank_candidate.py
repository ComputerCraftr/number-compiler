"""Candidate-only checks for the derived comma decimal-round quotient."""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Iterator
from dataclasses import replace
from pathlib import Path

import pytest

from devtools.checks.isabelle_syntax import parse_theory_header
from devtools.experiments.comma import generate_rank_candidate as generator
from devtools.paths import isabelle_root
from number_compiler.sequences.comma.boundary_chart import (
    UNIT_WEIGHT,
    BoundaryChart,
    ChartMove,
    chart_step,
)


def test_source_round_uses_canonical_chart_and_normalizes_phase() -> None:
    first = generator._decade_round_candidate(5, 3)
    assert first.kind == "continue"
    assert first.positions == 37
    assert first.terminal_chart == BoundaryChart("near", 9, 0, 3)
    assert first.successor == (6, 68)
    boundary, successor = generator._boundary_partial_round_candidate("Z", 7, 5)
    assert boundary.kind == "landmine"
    assert boundary.positions == 12
    assert successor is None
    near_boundary, near_successor = generator._boundary_partial_round_candidate(
        "N", 2, 10
    )
    assert near_boundary.kind == "continue"
    assert near_boundary.successor_chart == BoundaryChart("entry", 1, 1, 19)
    assert near_successor == (11, 19)


def test_cross_witness_checks_pre_cross_terminal_and_rejects_target() -> None:
    witness = generator._round_close_candidate(5, BoundaryChart("entry", 1, 0, 3))
    target = witness.successor_chart
    assert target is not None
    assert target == BoundaryChart("entry", 1, 1, 68)

    def checked_cross(candidate: generator.RoundClosure) -> bool:
        terminal = candidate.terminal_chart
        successor = candidate.successor_chart
        return (
            candidate.kind == "continue"
            and successor is not None
            and chart_step(5, terminal).next_chart == successor
            and terminal.kind == "near"
            and terminal.leading == 9
            and successor.kind == "entry"
            and successor.leading == 1
            and successor.delta == terminal.delta + 1
        )

    assert checked_cross(witness)
    assert not checked_cross(replace(witness, terminal_chart=target))
    # The malformed terminal is itself an Entry; its canonical edge cannot
    # be the crossing edge which the witness claims to have just consumed.
    assert chart_step(5, target).next_chart != target


def test_short_power_catalog_factors_entry_germs() -> None:
    periods, entry_cases = generator._phase_factorization_profile()
    assert len(periods) == 17
    assert sum(periods.values()) == 116
    assert entry_cases == 6_454
    assert Counter(periods.values()) == {
        1: 6,
        2: 1,
        3: 2,
        6: 5,
        22: 2,
        28: 1,
    }


def test_round_rejects_non_decreasing_or_unexpected_seam(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def non_decreasing(_residue: int, chart: BoundaryChart) -> ChartMove:
        return ChartMove(chart, UNIT_WEIGHT)

    monkeypatch.setattr(generator, "chart_step", non_decreasing)
    with pytest.raises(AssertionError, match="measure failed"):
        generator._decade_round_candidate(5, 3)

    def wrong_seam(_residue: int, chart: BoundaryChart) -> ChartMove:
        return ChartMove(BoundaryChart("entry", 2, chart.delta + 1, 0), UNIT_WEIGHT)

    monkeypatch.setattr(generator, "chart_step", wrong_seam)
    with pytest.raises(AssertionError, match="unproved decimal seam"):
        generator._decade_round_candidate(5, 3)


def test_internal_decade_graph_has_27_round_evaluations_and_no_cycle() -> None:
    graph = generator._decade_round_graph()
    ranks = generator._decade_rank_candidates(graph)
    assert len(graph) == len(ranks) == 924 * 91 == 84_084
    # Compare all checked-in candidate cells with independently recomputed edges.
    # Render the deliberately tiny data format; no second ML parser is needed.
    candidate_path = (
        isabelle_root(Path(__file__).resolve().parents[3])
        / "families/comma/comma_decade_rank_data/rank_candidates.ML"
    )
    encoded_rows = [
        '  "'
        + "".join(chr(ord("A") + rank) for rank in ranks[start : start + 91])
        + '"'
        for start in range(0, len(ranks), 91)
    ]
    expected = (
        "(* Untrusted ranks only. A=0, ..., Z=25, [=26. *)\n"
        "val comma_decade_candidate_rows = [\n" + ",\n".join(encoded_rows) + "\n];\n"
    )
    assert candidate_path.read_text() == expected
    assert min(ranks) == 0
    assert max(ranks) == 26  # Terminal state has rank zero.
    longest = next(index for index, rank in enumerate(ranks) if rank == 26)
    evaluations = 0
    while True:
        evaluations += 1
        successor = graph[longest].successor
        if successor is None:
            break
        longest = successor[0] * 91 + successor[1]
    assert evaluations == 27
    rows = generator._decade_rank_lines(graph, ranks)
    header = json.loads(next(rows))
    assert header["rank_meaning"] == "continuing_round_edges_not_boundary_safety"
    assert header["terminal_rank"] == 0
    assert header["max_rank"] == 26
    assert header["max_round_evaluations"] == 27
    assert header["first_max_source"] == [42, 68]
    assert len(header["first_max_chain"]) == 27
    assert header["first_max_chain"][-1] == [68, 10]
    assert generator._decade_round_candidate(68, 10).kind == "fork"
    first_phase = json.loads(next(rows))
    assert first_phase == {"phase": 0, "ranks": ranks[:91]}
    for candidate, rank in zip(graph, ranks, strict=True):
        successor = candidate.successor
        if successor is None:
            assert rank == 0
        else:
            child = successor[0] * 91 + successor[1]
            assert rank == ranks[child] + 1


def test_decade_candidate_streams_and_check_rejects_changed_line(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    graph = [generator._decade_round_candidate(5, 3)]
    monkeypatch.setattr(generator, "_decade_round_graph", lambda: graph)
    monkeypatch.setattr(generator, "_decade_rank_candidates", lambda _: [1])

    def lines(
        candidates: list[generator.DecadeRoundCandidate], ranks: list[int]
    ) -> Iterator[str]:
        assert candidates is graph and ranks == [1]
        yield json.dumps({"candidate_only": True}) + "\n"
        yield json.dumps({"rank": 1}) + "\n"

    monkeypatch.setattr(generator, "_decade_rank_lines", lines)
    path = tmp_path / "decade.jsonl"
    generator._write_decade_rank(path, check=False)
    generator._write_decade_rank(path, check=True)
    path.write_text('{"candidate_only": true}\n{"rank": 2}\n')
    with pytest.raises(SystemExit, match="differs"):
        generator._write_decade_rank(path, check=True)


def test_round_phase_ml_reproduces_and_rejects_corruption(tmp_path: Path) -> None:
    path = tmp_path / "phase-five.ML"
    generator._write_round_phase(path, 5, check=False)
    generator._write_round_phase(path, 5, check=True)
    text = path.read_text()
    equations = [line for line in text.splitlines() if "@{prop" in line]
    assert len(equations) == 91
    for offset, equation in enumerate(equations):
        assert f"comma_round_close 5 (Comma_Entry 1 0 {offset}) =" in equation
    assert "val comma_round_candidate_phase = 5;" in text
    path.write_text(text.replace("Comma_Near", "Comma_Entry", 1))
    with pytest.raises(SystemExit, match="round phase candidate differs"):
        generator._write_round_phase(path, 5, check=True)
    with pytest.raises(ValueError, match="round phase"):
        list(generator._round_phase_lines(924))


def test_decade_rank_data_does_not_import_transition_checker() -> None:
    theory = (
        isabelle_root(Path(__file__).resolve().parents[3])
        / "families/comma/comma_decade_rank_data/Comma_Decade_Rank_Data.thy"
    )
    name, imports = parse_theory_header(theory.read_text(), theory)
    assert name == "Comma_Decade_Rank_Data"
    assert imports == ("Comma_Decade_Totality.Comma_Decade_Control",)
