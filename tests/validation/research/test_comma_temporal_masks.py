"""Packed control is compared with canonical arithmetic, never used as proof."""

import pytest

from devtools.experiments.comma import temporal_masks
from devtools.experiments.comma.generate_rank_candidate import _decade_round_candidate
from devtools.experiments.comma.temporal_masks import (
    FULL_MASK,
    PhaseWord,
    SectorMaskCompiler,
    WordOutput,
    audit,
    offset_orbit,
    orbit_representatives,
    rotate_phase,
    square_words,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD


@pytest.mark.parametrize("advance", (0, 1, -1, 23, 923, 924, 1849))
def test_rotation_is_the_positive_phase_pullback(advance: int) -> None:
    mask = sum(1 << i for i in range(PERIOD) if i % 7 in (0, 3))
    rotated = rotate_phase(mask, advance)
    for phase in range(PERIOD):
        assert bool(rotated & (1 << phase)) == bool(
            mask & (1 << ((phase + advance) % PERIOD))
        )
    assert rotate_phase(rotated, -advance) == mask


def test_orbit_is_a_control_quotient_not_a_weight_quotient() -> None:
    reps = orbit_representatives()
    assert len(set(reps)) == 46
    assert [offset_orbit(x) for x in reps] == list(range(46))
    group = [x for x in range(91) if offset_orbit(x) == 0]
    assert group == [0, 1, 12, 33, 64]
    rows = [_decade_round_candidate(0, x) for x in group]
    assert len({(row.kind, row.successor, row.fork_a) for row in rows}) == 1
    assert [row.positions for row in rows] == [52, 51, 50, 49, 48]
    assert offset_orbit(2) == 45  # Truncated natural subtraction would give zero.


def test_sparse_squaring_preserves_phase_and_first_stop() -> None:
    early = (1 << 19) - 1
    live = WordOutput("live", 0)
    stop = WordOutput("fork", 3)
    base = (PhaseWord(((live, FULL_MASK ^ early), (stop, early))),) * 46
    words: tuple[PhaseWord, ...] = base
    span = 1
    for _ in range(5):
        words, _ = square_words(words, span)
        span *= 2
        for phase in range(PERIOD):
            expected = live
            for h in range(span):
                if early & (1 << ((phase + h) % PERIOD)):
                    expected = WordOutput("fork", 3, h)
                    break
            assert words[0].at(phase) == expected
    # Near the wrap the right half must see phase+span, not phase-span.
    assert words[0].at(PERIOD - 1) == WordOutput("fork", 3, 1)


@pytest.mark.parametrize(
    "leaves",
    (
        ((WordOutput("live", 0), FULL_MASK - 1),),
        ((WordOutput("live", 0), FULL_MASK), (WordOutput("fork", 2), 1)),
        ((WordOutput("live", 0), 1), (WordOutput("live", 0), FULL_MASK ^ 1)),
    ),
)
def test_incomplete_or_overlapping_partitions_are_rejected(
    leaves: tuple[tuple[WordOutput, int], ...],
) -> None:
    with pytest.raises(ValueError):
        PhaseWord(leaves)


def test_symbolic_control_matches_complete_finite_reference() -> None:
    result = audit(compare_reference=True)
    assert result["candidate_only"] is True
    assert result["production_admission"] is False
    assert result["base_scalar_evaluations"] == 0
    assert result["reference_scalar_evaluations"] == 42504
    assert result["boundary_scalar_evaluations"] == 0
    assert result["B32_live_outputs"] == 0
    assert result["B32_distinct_outputs"] == 204
    assert result["max_stop_crossings"] == 26
    assert result["max_losing_rank"] == 136
    assert result["losing_count"] == 14470
    assert result["survivors"] == result["source_cycle_length"] == 314
    assert result["source_cycle_gain"] == 924
    choices = result["source_cycle_choices"]
    assert isinstance(choices, str)
    # The separately established first fork contributes the initial zero.
    assert ("0" + choices).startswith("001110011101100001100101111110")


def test_boundary_requires_complete_control_and_valid_sector() -> None:
    compiler = SectorMaskCompiler()
    with pytest.raises(ValueError, match="46 complete stop words"):
        compiler.boundary_words(())
    live = PhaseWord(((WordOutput("live", 0), FULL_MASK),))
    with pytest.raises(ValueError, match="46 complete stop words"):
        compiler.boundary_words((live,) * 46)
    for leading, offset in ((0, 0), (10, 0), (1, -1), (1, 99)):
        with pytest.raises(ValueError, match="sector response"):
            compiler.word(leading, offset)
    assert not compiler.words and not compiler.branches


def test_symbolic_construction_does_not_call_scalar_reference(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object) -> object:
        raise AssertionError("symbolic constructor called the scalar round oracle")

    monkeypatch.setattr(temporal_masks, "_decade_round_candidate", forbidden)
    compiler = SectorMaskCompiler()
    word = compiler.word(1, 0)
    work = (compiler.chart_moves, compiler.intersections, len(compiler.words))
    assert compiler.word(1, 0) is word
    assert (compiler.chart_moves, compiler.intersections, len(compiler.words)) == work
    result = audit()
    assert result["B32_live_outputs"] == 0
    assert result["source_cycle_length"] == 314
