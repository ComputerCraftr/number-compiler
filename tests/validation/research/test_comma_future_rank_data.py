"""Candidate serialization is data transport, never a branch proof."""

from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

from devtools.experiments.comma import generate_rank_candidate as generator
from devtools.paths import isabelle_root

pytestmark = pytest.mark.validation


def _side_values(text: str) -> list[int]:
    body = text.split(" = [", 1)[1].split(']"', 1)[0]
    return [int(value) for value in re.findall(r"\d+", body)]


def test_rank_default_output_has_concrete_check_owner() -> None:
    assert generator.DEFAULT_OUTPUT == (
        isabelle_root(Path(__file__).resolve().parents[3])
        / "families/comma/comma_future_rank_data/Comma_Rank_Data.thy"
    )


def test_rank_side_split_preserves_every_catalog_index() -> None:
    codes = list(range(generator.PADDED_COUNT))
    near = _side_values(generator._render_rank_side("N", codes))
    zero = _side_values(generator._render_rank_side("Z", codes))
    side_count = generator.STATE_COUNT // 2
    assert near[:side_count] == codes[:side_count]
    assert zero[:side_count] == codes[side_count : 2 * side_count]
    assert near[side_count:] == zero[side_count:] == [0] * (8192 - side_count)
    for index in range(generator.STATE_COUNT):
        selected = near if index < side_count else zero
        local = index % side_count
        # The emitted HOL lookup traverses the same four radix-16 levels.
        digits = (local // 4096, (local // 256) % 16, (local // 16) % 16, local % 16)
        flat = ((digits[0] * 16 + digits[1]) * 16 + digits[2]) * 16 + digits[3]
        assert selected[flat] == codes[index]


def test_rank_generator_checks_both_semantic_side_files(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    output = tmp_path / "Comma_Rank_Data.thy"
    authored = "authored fail-closed lookup and its checked lemmas\n"
    output.write_text(authored)
    codes = [0] * generator.PADDED_COUNT
    monkeypatch.setattr(generator, "_candidate_ranks", lambda: codes)
    monkeypatch.setattr(
        sys, "argv", ["generate_rank_candidate", "--output", str(output)]
    )
    generator.main()
    assert output.read_text() == authored
    assert set(tmp_path.iterdir()) == {
        output,
        tmp_path / "Comma_Rank_Data_N.thy",
        tmp_path / "Comma_Rank_Data_Z.thy",
    }
    monkeypatch.setattr(
        sys, "argv", ["generate_rank_candidate", "--output", str(output), "--check"]
    )
    generator.main()
    assert output.read_text() == authored
    (tmp_path / "Comma_Rank_Data_Z.thy").write_text("corrupted candidate")
    with pytest.raises(SystemExit, match="Comma_Rank_Data_Z"):
        generator.main()
