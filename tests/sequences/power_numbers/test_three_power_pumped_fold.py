from __future__ import annotations

import pytest

from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.sequences.power_numbers.fermat_binary_pair_fold import (
    FermatBinaryFoldAction,
    FermatBinarySLPSnapshot,
    fold_binary_slp,
)
from number_compiler.sequences.power_numbers.three_power_pumped_fold import (
    GuardedBinarySource,
)
from tests.support.fermat_guarded_source_oracle import (
    literal_fermat_residue,
    literal_radial_width,
    literal_toggle_runs,
)
from tests.support.private_attributes import private_test_attribute


def _source(bits: tuple[int, ...]) -> tuple[SLPArena, int, GuardedBinarySource]:
    arena = SLPArena()
    root = arena.word(bits)
    return arena, root, GuardedBinarySource.admit(arena, root)


def _binary_lsd(value: int) -> tuple[int, ...]:
    return tuple((value >> offset) & 1 for offset in range(value.bit_length()))


def test_binary_slp_fold_and_guarded_default_edit_match_literal_source() -> None:
    bits = (1, 0, 0, 1, 1)
    arena, root, source = _source(bits)

    edited = source.toggle_run(1, 2, 0)
    expected = literal_toggle_runs(bits, edited.edits)

    folded = edited.fold(2)
    assert folded.length == len(expected)
    assert folded.residue == literal_fermat_residue(expected, 2)
    triple = edited.triple_fold(2)
    assert triple.source_length == len(expected)
    assert triple.residue == literal_fermat_residue(expected, 2) * 3 % 5
    assert fold_binary_slp(arena, root, width=2).residue == literal_fermat_residue(
        bits, 2
    )


def test_source_snapshot_is_immutable_and_binding_rejects_foreign_handles() -> None:
    bits = (1, 0, 1, 1)
    arena, root, source = _source(bits)
    expected = literal_fermat_residue(bits, 3)

    # Poisoning the construction arena cannot trigger a replay after admission.
    arena.nodes[root] = SLPNode(root, "BROKEN", 1)
    assert source.fold(3).residue == expected
    assert (
        source.radial_width_observation().tripled_bits == literal_radial_width(bits)[2]
    )

    with pytest.raises(ValueError, match="another arena/root"):
        source.require_binding(SLPArena(), root)
    with pytest.raises(ValueError, match="another arena/root"):
        source.require_binding(arena, arena.empty())


def test_compressed_radial_width_uses_repeats_without_materializing() -> None:
    arena = SLPArena()
    block = arena.word((0, 1))
    root = arena.repeat(block, 10**10)
    source = GuardedBinarySource.admit(arena, root)

    observation = source.radial_width_observation()

    assert observation.source_bits == 20_000_000_000
    assert observation.threshold_comparison == -1
    assert observation.tripled_bits == 20_000_000_001


def test_radial_width_rejects_noncanonical_leading_bit_and_bad_guard() -> None:
    _, _, source = _source((1, 0))
    with pytest.raises(ValueError, match="leading one"):
        source.radial_width_observation()
    with pytest.raises(ValueError, match="guard"):
        source.toggle_run(1, 1, 1)


@pytest.mark.parametrize("value", (1, 2, 3, 5, 6, 7, 10, 11, 12, 21, 22, 23))
def test_radial_width_matches_threshold_edges(value: int) -> None:
    bits = _binary_lsd(value)
    _, _, source = _source(bits)

    observation = source.radial_width_observation()

    assert (
        observation.source_bits,
        observation.threshold_comparison,
        observation.tripled_bits,
    ) == literal_radial_width(bits)


def test_overlapping_guarded_runs_compose_against_the_current_source() -> None:
    bits = (1, 1, 1, 1, 1)
    _, _, source = _source(bits)
    edited = source.toggle_run(1, 3, 1).toggle_run(2, 2, 0)
    expected = literal_toggle_runs(bits, edited.edits)

    assert expected == (1, 0, 1, 1, 1)
    assert edited.fold(3).residue == literal_fermat_residue(expected, 3)
    assert (
        edited.radial_width_observation().tripled_bits
        == literal_radial_width(expected)[2]
    )


def test_snapshot_preflights_malformed_child_before_length_arithmetic() -> None:
    arena = SLPArena()
    left = arena.terminal(1)
    right = arena.terminal(0)
    root = arena.concat(left, right)
    arena.nodes[left] = SLPNode(left, "TERM", True, symbol=1)

    with pytest.raises(ValueError, match="exact integers"):
        FermatBinarySLPSnapshot.admit(arena, root)


def test_population_counts_are_lazy_for_signed_fold_admission() -> None:
    arena = SLPArena()
    block = arena.word((1, 0, 1))
    root = arena.repeat(block, 1 << 350)
    snapshot = FermatBinarySLPSnapshot.admit(arena, root)

    assert private_test_attribute(snapshot, "_one_counts") is None
    before_hash = hash(snapshot)
    equivalent = FermatBinarySLPSnapshot.admit(arena, root)
    assert snapshot == equivalent
    assert hash(snapshot) == hash(equivalent)
    snapshot.fold(width=7)
    assert private_test_attribute(snapshot, "_one_counts") is None
    ones, visits = snapshot.count_ones(0, snapshot.nodes[snapshot.root].length)
    assert ones == 2 * (1 << 350)
    assert visits > 0
    assert private_test_attribute(snapshot, "_one_counts") is not None
    assert hash(snapshot) == before_hash
    assert snapshot == equivalent
    assert {snapshot: "stable"}[equivalent] == "stable"


def test_aligned_signed_width_repeats_match_ordered_composition() -> None:
    for width in (1, 2, 5, 9):
        modulus = (1 << width) + 1
        for length in (2 * width, width):
            action = FermatBinaryFoldAction(width, length, modulus - 2)
            for count in (0, 1, 2, 3, 8, 17):
                expected = FermatBinaryFoldAction.identity(width)
                for _ in range(count):
                    expected = expected.then(action)
                assert action.repeat(count) == expected

    # A nonaligned action still uses the ordered general composition path.
    action = FermatBinaryFoldAction(7, 10, 19)
    expected = FermatBinaryFoldAction.identity(7)
    for _ in range(13):
        expected = expected.then(action)
    assert action.repeat(13) == expected
