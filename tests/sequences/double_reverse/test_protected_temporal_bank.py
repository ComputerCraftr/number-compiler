"""Independent physical oracles for guarded source-generated GT/EQ/LT powers."""

from __future__ import annotations

import json
from dataclasses import fields

import pytest

from number_compiler.api import cli, cli_render
from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.metric_keys.double_reverse import (
    DOUBLE_REVERSE_PERIODIC_BANK_MOORE_CONSTRUCTIONS,
    DOUBLE_REVERSE_PERIODIC_BANK_MOORE_OUTPUT_EVALUATIONS,
    DOUBLE_REVERSE_PERIODIC_BANK_TEMPORAL_STATES,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.protected_temporal_bank import (
    PERIODIC_CHANNELS,
    ProtectedPeriodicBank,
    certified_periodic_region,
    protected_periodic_bank,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import growth_ports
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    UncertifiedPointedStencilError,
)


def literal_t(x: int) -> int:
    return 2 * int(str(x)[::-1])


@pytest.mark.parametrize(
    "upper,lower,phase",
    [("17", "88", 0), ("17", "42", 1), ("48", "42", 2), ("48", "88", 3)],
)
@pytest.mark.parametrize(
    "word,period", [("48", 2), ("59", 2), ("90", 2), ("01", 2), ("123", 3), ("3", 1)]
)
def test_periodic_bank_matches_literally_evolved_symmetric_rays(
    upper: str, lower: str, phase: int, word: str, period: int
) -> None:
    middle = word * (60 // len(word))
    seed = int(upper + middle + lower)
    # Nine F-steps make the phase-dependent births asymmetric for phases 0
    # and 2, so swapping L and R in the right coordinate cannot pass.
    f_steps, coordinate = 9, 20
    source_width = len(str(seed))
    with DoubleReverseTerm(seed, 2 * f_steps) as term:
        engine = term._adapter.temporal_hashlife
        assert engine.certify(term._source.root) == phase
        bank = term.protected_temporal_bank(coordinate, period=period)
        assert bank.represented_steps == f_steps
        assert bank.physical_prefix == 0
        assert set(bank.counts()) == set(PERIODIC_CHANNELS)
        value = seed
        expected_counts = dict.fromkeys(PERIODIC_CHANNELS, 0)
        for tick in range(f_steps):
            frame = bank.at(tick)
            source = str(value)
            left, right = growth_ports(phase, tick)
            assert len(source) == source_width + left + right
            left_position = coordinate + left
            right_position = source_width - 1 - coordinate + right
            actual = (
                int(source[left_position]),
                int(source[right_position]),
            )
            # Both positions reflect across the actual changing width:
            # left=i+L, right=w-1-i+R, and L+R is total growth.
            assert left_position + right_position == len(source) - 1
            assert frame.digits == actual
            pair = sum(actual)
            assert frame.pair == pair
            assert (
                frame.lt_low,
                frame.lt_high,
                frame.eq,
                frame.gt_low,
                frame.gt_high,
            ) == (
                int(pair < 5),
                int(5 <= pair <= 8),
                int(pair == 9),
                int(10 <= pair <= 14),
                int(15 <= pair <= 18),
            )
            assert frame.carry_xor == ((actual[0] >= 5) ^ (actual[1] >= 5))
            for channel in PERIODIC_CHANNELS:
                expected_counts[channel] += frame.scalar(channel)
            value = literal_t(literal_t(value))
            next_s = str(value)
            next_left, next_right = growth_ports(phase, tick + 1)
            assert len(next_s) == source_width + next_left + next_right
            next_pair = (
                int(next_s[coordinate + next_left]),
                int(next_s[source_width - 1 - coordinate + next_right]),
            )
            assert frame.next_digits == next_pair
            assert frame.borrow_left == (
                int(next_pair[0] < actual[0]),
                int(next_pair[0] < actual[0] + 1),
            )
            assert frame.borrow_right == (
                int(next_pair[1] < actual[1]),
                int(next_pair[1] < actual[1] + 1),
            )
            next_birth_left, next_birth_right = growth_ports((phase + 2 * tick) % 4, 1)
            assert (frame.growth_left, frame.growth_right) == (
                next_birth_left,
                next_birth_right,
            )
            assert frame.growth == next_birth_left + next_birth_right
        assert bank.counts() == expected_counts
        assert term._image is None
        assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1


def test_periodicity_guard_uses_exact_slp_repeat_without_expansion() -> None:
    arena = SLPArena()
    huge = arena.repeat(arena.word([4, 8]), 10**12)
    assert certified_periodic_region(arena, huge, 10**6, 10**12, 0, (4, 8))
    assert not certified_periodic_region(arena, huge, 10**6, 10**12, 0, (8, 4))
    assert certified_periodic_region(arena, huge, 10**6 + 1, 10**12, 1, (8, 4))


def test_guard_rejects_one_wrong_interior_digit_and_missing_halo() -> None:
    text = "17" + "48" * 30 + "88"
    seed = int(text)
    with DoubleReverseTerm(seed, 20) as term:
        assert term.protected_temporal_bank(20, period=2).f_steps == 10
        with pytest.raises(UncertifiedPointedStencilError, match="halo"):
            term.protected_temporal_bank(0, period=2)
        with pytest.raises(UncertifiedPointedStencilError, match="periodic"):
            term.protected_temporal_bank(20, period=1)
    mutated = text[:27] + ("9" if text[27] != "9" else "5") + text[28:]
    with (
        DoubleReverseTerm(int(mutated), 20) as term,
        pytest.raises(UncertifiedPointedStencilError, match="periodic"),
    ):
        term.protected_temporal_bank(20, period=2)


def test_temporal_moore_does_not_conflate_different_gt_high_outputs() -> None:
    # Alternating paired rays have GT-high innovations even while a shared
    # two-cell border remains in the same unconditional 4-phase cylinder.
    seed = int("17" + "48" * 30 + "88")
    with DoubleReverseTerm(seed, 20) as term:
        bank = term.protected_temporal_bank(20, period=2)
        values = [bank.at(tick).gt_high for tick in range(10)]
        assert 0 in values and 1 in values
        assert bank.moore_classes is not None
        assert bank.moore_classes["gt_high"] > 1
        assert bank.moore_classes["eq"] == 1
        metrics = term.metrics()
        temporal_states = metrics[DOUBLE_REVERSE_PERIODIC_BANK_TEMPORAL_STATES]
        assert metrics[DOUBLE_REVERSE_PERIODIC_BANK_MOORE_CONSTRUCTIONS] == 16
        # Fifteen scalar projections plus the joint scalar-output projection.
        assert (
            metrics[DOUBLE_REVERSE_PERIODIC_BANK_MOORE_OUTPUT_EVALUATIONS]
            == 30 * temporal_states
        )


def test_protected_bank_readers_require_live_unchanged_source_authority() -> None:
    seed = int("17" + "48" * 30 + "88")

    def read_at(record: ProtectedPeriodicBank) -> object:
        return record.at(0)

    def read_counts(record: ProtectedPeriodicBank) -> object:
        return record.counts()

    def read_extent(record: ProtectedPeriodicBank) -> object:
        return record.represented_steps

    readers = (read_at, read_counts, read_extent)
    with DoubleReverseTerm(seed, 20) as term:
        bank = term.protected_temporal_bank(20, period=2)
        forged = type(bank)(
            **{field.name: getattr(bank, field.name) for field in fields(type(bank))}
        )
        for read in readers:
            with pytest.raises(ValueError, match="source authority"):
                read(forged)

        original_steps = bank.f_steps
        object.__setattr__(bank, "f_steps", original_steps + 1)
        for read in readers:
            with pytest.raises(ValueError, match="source authority"):
                read(bank)
        object.__setattr__(bank, "f_steps", original_steps)
        assert bank.represented_steps == original_steps

    with pytest.raises(ValueError, match="source authority"):
        bank.at(0)
    with pytest.raises(ValueError, match="source authority"):
        bank.counts()
    with pytest.raises(ValueError, match="source authority"):
        _ = bank.represented_steps


def test_prefix_to_cylinder_closed_form_is_explicit_not_fabricated() -> None:
    with DoubleReverseTerm(196, 64) as term:
        form = term.temporal_closed_form()
        assert form.phase_in is None  # Original seed is outside the cylinder.
        assert form.affine_gain is None
        assert form.prefix_steps == 16
        assert form.entry_value == 173488
        assert form.suffix_steps == 48
        assert form.suffix_phase_in == form.suffix_phase_out == 0
        assert form.suffix_affine_gain is not None
        assert form.suffix_affine_gain == 160**12
        assert form.suffix_affine_shift is not None
        assert form.target == (
            form.suffix_affine_gain * form.entry_value + form.suffix_affine_shift
        )
        assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1
    with DoubleReverseTerm(196, 64) as term:
        form = term.temporal_closed_form(modulus=97)
        assert form.prefix_steps == 16
        assert form.suffix_affine_gain is not None
        assert form.suffix_affine_gain == pow(160, 12, 97)
        assert form.entry_value is not None
        assert form.suffix_affine_shift is not None
        assert (
            form.suffix_affine_gain * form.entry_value + form.suffix_affine_shift
        ) % 97 == form.target
    with DoubleReverseTerm(50, 2) as term:
        form = term.temporal_closed_form()
        assert form.suffix_affine_gain is None


def test_temporal_grammar_cli_does_not_build_endpoint(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    def forbid(_term: DoubleReverseTerm) -> None:
        raise AssertionError("periodic temporal bank rebuilt the complete endpoint")

    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", forbid)
    monkeypatch.setattr(cli_render, "_render_value", forbid)
    seed = "17" + "48" * 30 + "88"
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                seed,
                "--nth",
                "20",
                "--no-value",
                "--info",
                "temporal.grammar",
                "--temporal-grammar-position",
                "20",
                "--temporal-grammar-period",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    result = json.loads(capsys.readouterr().out)["info"]["temporal.grammar"]
    assert result["status"] == "available"
    assert result["f_steps"] == result["represented_steps"] == 10
    assert result["counts"]["gt_high"] > 0
    assert result["left_region"] == [10, 31]
    assert result["right_region"] == [33, 54]
    assert result["source_width"] == 64
    assert result["position_unit"] == "entry_outer_to_inner_pair"
    assert result["region_unit"] == "entry_source_half_open_digits"


def test_bad_boundary_cannot_authorize_protected_grammar() -> None:
    with (
        DoubleReverseTerm(0, 20) as term,
        pytest.raises(UncertifiedPointedStencilError),
    ):
        term.protected_temporal_bank(3, period=2)


def test_billion_digit_slp_period_and_temporal_word_are_pumped() -> None:
    arena = SLPArena()
    source = arena.concat_many(
        (
            arena.word((1, 7)),
            arena.repeat(arena.terminal(3), 10**9),
            arena.word((8, 8)),
        )
    )
    bank = protected_periodic_bank(arena, source, 0, 500, 100, 1)
    assert bank.represented_steps == 100
    assert bank.repeat_count == 50
    assert len(bank.motif) == 2
    assert bank.counts()["lt_high"] == 100
    assert bank.counts()["gt_high"] == 0
    assert bank.moore_classes is not None
    assert bank.moore_classes["joint"] < 3
    assert len(arena.nodes) < 20
    with pytest.raises(ValueError, match="certified"):
        protected_periodic_bank(arena, source, 2, 500, 100, 1)


def test_exact_pair_oracle_matches_full_term_without_materializing_it() -> None:
    depths = (18, 32, 63, 64, 100)
    for seed in (196, 12, 173488, 174388, 1768742):
        checkpoints: dict[int, str] = {}
        x = seed
        for current_depth in range(1, max(depths) + 1):
            x = literal_t(x)
            if current_depth in depths:
                checkpoints[current_depth] = str(x)
        for depth in depths:
            word = checkpoints[depth]
            with DoubleReverseTerm(seed, depth) as term:
                for pair_position in range(min(4, len(word) // 2)):
                    pair = term.exact_temporal_pair(pair_position)
                    expected = (int(word[pair_position]), int(word[-1 - pair_position]))
                    pair_sum = sum(expected)
                    assert pair.digits == expected
                    assert pair.pair == pair_sum
                    assert pair.gt_high == int(pair_sum >= 15)
                    assert pair.eq == int(pair_sum == 9)
                assert term._image is None
                assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1


def test_pointed_pairs_reuse_the_owner_issued_prefix_without_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbid_endpoint(_term: DoubleReverseTerm) -> None:
        raise AssertionError("pointed pair constructed the complete endpoint")

    with DoubleReverseTerm(196, 64, max_steps=128) as term:
        monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", forbid_endpoint)
        first = term.exact_temporal_pair(1)
        prefix_steps = term.metrics()["double_reverse_pointed_border_entry_steps"]
        assert first.physical_prefix == 16
        assert prefix_steps == 16
        for position in (0, 2, 3):
            term.exact_temporal_pair(position)
        assert (
            term.metrics()["double_reverse_pointed_border_entry_steps"] == prefix_steps
        )
        assert term._image is None
        assert term.metrics()["double_reverse_pointed_stencil_publications"] == 8


def test_exact_pair_cli_observer(capsys: pytest.CaptureFixture[str]) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "64",
                "--no-value",
                "--info",
                "spatial.pair-bank",
                "--spatial-pair-bank-position",
                "1",
                "--format",
                "json",
            ]
        )
        == 0
    )
    result = json.loads(capsys.readouterr().out)["info"]["spatial.pair-bank"]
    assert result["pair"] == 15
    assert result["gt_high"] == 1
    assert result["eq"] == 0
    assert result["physical_prefix"] == 16
    assert result["digits"] == [7, 8]
