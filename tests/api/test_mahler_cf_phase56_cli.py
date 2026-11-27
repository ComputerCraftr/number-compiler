"""The public cylinder uses complete six-column ordered suffix actions."""

from __future__ import annotations

import json

import pytest

from number_compiler.api.cli import main
from number_compiler.sequences.antihydra import mahler_cf_reciprocal_tile as tiles
from number_compiler.sequences.antihydra.mahler_cf_low_period import settled_low_action
from tests.sequences.antihydra.test_mahler_pow5_ordered_blocks import literal_segment


def test_public_cylinder_reads_heads_after_complete_phase_actions(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_CF_RECIPROCAL", "1")
    monkeypatch.delenv("NUMBER_COMPILER_ENABLE_CF_CONTINUANT", raising=False)
    args = [
        "antihydra",
        "--nth",
        "0",
        "--no-value",
        "--format",
        "json",
        "--info",
        "arithmetic.continued-fraction",
        "--safety-horizon",
        "4096",
    ]
    with monkeypatch.context() as oracle:
        oracle.setattr(tiles.ReciprocalTile, "segment", literal_segment)
        assert main(args) == 0
        expected = json.loads(capsys.readouterr().out)

    selected: dict[int, set[int]] = {5: set(), 6: set()}
    head_digits = 0
    interval = tiles.reciprocal_row_interval

    def select(exponent: int, columns: int) -> tuple[int, int, int, int]:
        action = settled_low_action(exponent, columns)
        if columns in selected:
            selected[columns].add((exponent - columns) % (1 << (columns - 2)))
        return action

    def head(q: int, t: int, width: int, start: int, count: int) -> int:
        nonlocal head_digits
        head_digits += count
        return interval(q, t, width, start, count)

    monkeypatch.setattr(tiles, "settled_low_action", select)
    monkeypatch.setattr(tiles, "reciprocal_row_interval", head)
    assert main(args) == 0
    packet = json.loads(capsys.readouterr().out)
    assert packet == expected
    assert packet["info"]["arithmetic.continued-fraction"]["coefficient_count"] == 540
    assert selected[5] and len(selected[6]) > 1
    assert head_digits < 465
