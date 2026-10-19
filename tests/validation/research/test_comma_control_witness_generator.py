"""Bounded checks for untrusted comma control-position candidates."""

from __future__ import annotations

import json
import sys
from collections.abc import Iterator
from pathlib import Path

import pytest

from devtools.experiments.comma import generate_rank_candidate as generator
from devtools.experiments.comma.generate_rank_candidate import (
    _control_witness,
    _witness_slices,
    control_witness_from_chart,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD, BoundaryChart


def test_first_winning_boundary_control_candidate() -> None:
    witness = _control_witness("N", 2, 10)
    assert witness["source"] == {"kind": "N", "a": 2, "residue": 10}
    assert witness["start"] == ["near", 1, 0, 1]
    assert witness["depth"] == len(witness["positions"]) == 93
    assert witness["outcome"] == {"kind": "fork", "a": 7, "delta": 2}
    assert witness["phase_normalization"] == [
        {"delta": 0, "residue": 10},
        {"delta": 1, "residue": 11},
        {"delta": 2, "residue": 12},
    ]
    assert "endpoint" not in witness
    assert "weight" not in witness
    assert json.loads(json.dumps(witness)) == witness


def test_tiny_landmine_control_candidate() -> None:
    witness = _control_witness("Z", 7, 5)
    assert witness["start"] == ["entry", 7, 0, 0]
    assert witness["depth"] == len(witness["positions"]) == 12
    assert witness["outcome"] == {"kind": "landmine", "delta": 0}
    assert witness["positions"][-1] == ["near", 9, 0, 28]
    assert witness["phase_normalization"] == [{"delta": 0, "residue": 5}]


def test_intermediate_entry_candidate_keeps_exact_start() -> None:
    start = BoundaryChart("entry", 1, 0, 3)
    witness = control_witness_from_chart(start, 5)
    assert witness["source"] == {
        "chart": ["entry", 1, 0, 3],
        "residue": 5,
    }
    assert witness["start"] == ["entry", 1, 0, 3]
    assert witness["depth"] == len(witness["positions"]) == 230
    assert witness["outcome"] == {"kind": "fork", "a": 2, "delta": 5}


def test_witness_slices_are_complete_and_selectable() -> None:
    all_slices = _witness_slices(None, None)
    assert len(all_slices) == 16
    assert all_slices[0] == ("N", 2)
    assert all_slices[-1] == ("Z", 9)
    assert _witness_slices("Z", 7) == [("Z", 7)]
    assert 16 * PERIOD == 14_784


def test_witness_only_never_builds_rank_candidate(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    calls: list[tuple[Path, bool]] = []

    def poison_rank() -> list[int]:
        raise AssertionError("rank construction was requested")

    def capture_slices(
        directory: Path,
        *,
        kind: str | None,
        a: int | None,
        check: bool,
    ) -> None:
        assert kind == "Z" and a == 7
        calls.append((directory, check))

    monkeypatch.setattr(generator, "_candidate_ranks", poison_rank)
    monkeypatch.setattr(generator, "_write_witness_slices", capture_slices)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "generate_rank_candidate.py",
            "--witness-only",
            "--witness-dir",
            str(tmp_path),
            "--witness-kind",
            "Z",
            "--witness-a",
            "7",
        ],
    )
    generator.main()
    assert calls == [(tmp_path, False)]


def test_witness_slice_write_and_check_stream_lines(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    def two_lines(kind: str, a: int) -> Iterator[str]:
        assert (kind, a) == ("Z", 7)
        yield '{"candidate_only":true}\n'
        yield '{"depth":12}\n'

    monkeypatch.setattr(generator, "_witness_slice_lines", two_lines)
    generator._write_witness_slices(tmp_path, kind="Z", a=7, check=False)
    path = tmp_path / "comma-control-Z-7.jsonl"
    assert path.read_text() == '{"candidate_only":true}\n{"depth":12}\n'
    generator._write_witness_slices(tmp_path, kind="Z", a=7, check=True)
    path.write_text('{"candidate_only":true}\n{"depth":11}\n')
    with pytest.raises(SystemExit, match="differs"):
        generator._write_witness_slices(tmp_path, kind="Z", a=7, check=True)
