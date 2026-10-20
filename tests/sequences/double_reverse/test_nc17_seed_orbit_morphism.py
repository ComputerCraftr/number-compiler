"""Seed-specific NC17 full-word temporal morphism / outer-inner join."""

from __future__ import annotations

from copy import copy
from dataclasses import replace

import pytest

from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_center_selector import (
    center_return,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    UncertifiedPointedStencilError,
)
from number_compiler.sequences.double_reverse.temporal_seed_morphism import (
    CertifiedSeedOrbitMorphism,
    SeedWordFiber,
    word_fiber_from_root,
)
from tests.support.reverse_add_source_data import iterate_double_reverse


def assert_fiber_matches_word(fiber: SeedWordFiber, word: str) -> None:
    # Only the TEST reads the full expected word. The producer builds its
    # independent modular folds and center with SLP interval operations.
    width = len(word)
    middle_width = 1 if width & 1 else 2
    s = (width - middle_width) // 2
    center = tuple(int(c) for c in word[s : s + middle_width])
    exterior = int(word[:s] or "0") * 10 ** (s + middle_width) + int(
        word[s + middle_width :] or "0"
    )
    assert fiber.width == width
    assert fiber.center == center
    assert fiber.residue99 == int(word) % 99
    assert fiber.residue198 == int(word) % 198
    assert fiber.exterior99 == exterior % 99
    assert fiber.exterior198 == exterior % 198
    if middle_width == 2:
        assert fiber.center_band_moore in range(24)
    else:
        assert fiber.center_band_moore is None


@pytest.mark.parametrize("n", (20, 24, 32, 64, 128, 256))
def test_seed196_whole_word_power_and_punctured_outer_ring(n: int) -> None:
    previous = str(iterate_double_reverse(196, 16))
    expected = str(iterate_double_reverse(196, n))
    with DoubleReverseTerm(196, n, max_state_bits=16384) as term:
        action = term.temporal_seed_orbit_morphism((n - 16) // 2)
        assert action.physical_interval == (16, n)
        assert action.physical_prefix == 16
        assert action.source_phase == 0
        assert not action.all_depth_period_claim
        assert_fiber_matches_word(action.first, previous)
        assert_fiber_matches_word(action.last, expected)
        assert action.residue_action.duration == n - 16
        assert action.residue_action.target_mod99 == int(expected) % 99
        assert action.residue_action.target_mod198 == int(expected) % 198
        assert (
            action.last.width
            == action.first.width + action.left_births + action.right_births
        )
        assert tuple(action.digit_at(k) for k in range(action.last.width)) == tuple(
            map(int, expected)
        )
        assert tuple(
            action.digit_at(k, after=False) for k in range(action.first.width)
        ) == tuple(map(int, previous))
        with pytest.raises(IndexError):
            action.digit_at(action.last.width)
        action.validate_source_authority()
        with pytest.raises(ValueError, match="authority"):
            copy(action).validate_source_authority()
    with pytest.raises(ValueError, match="authority"):
        action.validate_source_authority()


def test_public_word_fiber_root_rejects_bool_and_foreign_indices() -> None:
    with DoubleReverseTerm(196, 20, max_state_bits=16384) as term:
        _owner, source = term.prepare_bank_source(max_prefix=32)
        arguments = (source.arena, source.ledger, source.scratch_owner)
        with pytest.raises(TypeError, match="exact integer"):
            word_fiber_from_root(*arguments, True)
        with pytest.raises(ValueError, match="outside"):
            word_fiber_from_root(*arguments, -1)
        with pytest.raises(ValueError, match="outside"):
            word_fiber_from_root(*arguments, len(source.arena.nodes))


@pytest.mark.parametrize("power", range(7))
def test_seed196_dyadic_square_is_exact_fiber_morphism(power: int) -> None:
    n = 16 + 2 * (1 << power)
    with DoubleReverseTerm(196, n, max_state_bits=16384) as term:
        action = term.temporal_seed_orbit_morphism_power_of_two(power)
        expected = str(iterate_double_reverse(196, n))
        assert action.steps == 1 << power
        assert action.physical_interval == (16, n)
        assert_fiber_matches_word(action.last, expected)
        assert not action.all_depth_period_claim
        action.validate_source_authority()


def test_seed196_joint_square_uses_actual_midroot_not_replayed_word(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(196, 144, max_state_bits=16384) as term:
        # The genuine 16-physical-step transient must be issued once, then
        # the powered suffix is forbidden from using either scalar adapter.
        _, pointed = term.prepare_bank_source(max_prefix=32)
        assert pointed.physical_prefix == 16
        assert pointed.f_steps == 64

        def forbid_scalar(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("powered seed morphism replayed scalar arithmetic")

        monkeypatch.setattr(type(term.source_adapter), "_apply_word", forbid_scalar)
        monkeypatch.setattr(
            type(term.source_adapter), "_general_two_step", forbid_scalar
        )
        start = term.temporal_seed_orbit_morphism(1)
        current = start
        for exponent in range(1, 7):
            current = term.temporal_seed_orbit_morphism_square(current)
            until = 16 + 2 * (1 << exponent)
            assert current.steps == 1 << exponent
            assert current.physical_interval == (16, until)
            assert_fiber_matches_word(
                current.last, str(iterate_double_reverse(196, until))
            )
        assert current.last.root != current.first.root
        assert current.first.root == pointed.root
        assert current.last.center == (5, 0)
        metrics = term.metrics()
        assert metrics["double_reverse_hashlife_cones"] > 0
        assert metrics["double_reverse_spatial_transducer_applications"] == 0


def test_seed196_true_four_tick_carry_driver_and_two_block_composition() -> None:
    with DoubleReverseTerm(196, 24) as term:
        first = term.temporal_seed_orbit_morphism(2)
        assert first.physical_interval == (16, 20)
        assert first.four_step_driver is not None
        assert first.three_odd_centers is not None
        initial = (first.first.center[0], first.first.center[1])
        result = center_return(initial, first.four_step_driver)
        assert result.odd == first.three_odd_centers
        assert result.next_pair == first.last.center
        doubled = term.temporal_seed_orbit_morphism_square(first)
        assert doubled.steps == 4
        assert doubled.physical_interval == (16, 24)
        assert doubled.four_step_driver is None  # not an invented repeated word
        assert_fiber_matches_word(doubled.last, str(iterate_double_reverse(196, 24)))
        with pytest.raises(UncertifiedPointedStencilError, match="source-certified"):
            term.temporal_seed_orbit_morphism_square(doubled)


def test_reject_cross_root_tampering_and_out_of_horizon() -> None:
    with (
        DoubleReverseTerm(196, 32) as term,
        DoubleReverseTerm(196, 32) as foreign,
    ):
        first = term.temporal_seed_orbit_morphism(2)
        other = foreign.temporal_seed_orbit_morphism(2)
        with pytest.raises(ValueError, match="source/root adjacency"):
            first.then(other)
        with pytest.raises(UncertifiedPointedStencilError, match="source-certified"):
            foreign.temporal_seed_orbit_morphism_square(first)
        with pytest.raises(ValueError, match="authority"):
            replace(first, steps=4).validate_source_authority()
        with pytest.raises(UncertifiedPointedStencilError, match="horizon"):
            term.temporal_seed_orbit_morphism(9)
        with pytest.raises(ValueError, match="adjacency"):
            first.then(first)
        assert term.temporal_seed_orbit_morphism_square(first).steps == 4


def test_other_cylinder_seed_and_00_99_center_remain_exact_not_guessed() -> None:
    seed = int("17" + "48" * 12 + "88")
    with DoubleReverseTerm(seed, 16) as term:
        action = term.temporal_seed_orbit_morphism(8)
        assert action.physical_interval == (0, 16)
        assert_fiber_matches_word(action.last, str(iterate_double_reverse(seed, 16)))
        assert isinstance(action, CertifiedSeedOrbitMorphism)
    # The scalar quotient leaves this central pair ambiguous in a bank-only
    # inference, but the full-word source-root morphism retains the true pair.
    with DoubleReverseTerm(170688, 4) as term:
        word = str(iterate_double_reverse(170688, 4))
        action = term.temporal_seed_orbit_morphism(2)
        assert action.last.center in ((0, 0), (9, 9))
        assert_fiber_matches_word(action.last, word)


def test_seed196_120_tick_cyclotomic_return_does_not_force_center_return() -> None:
    with DoubleReverseTerm(196, 136) as term:
        action = term.temporal_seed_orbit_morphism(60)
        assert action.physical_interval == (16, 136)
        assert action.global_four_block_order == 30
        assert action.first.residue99 == action.last.residue99 == 40
        assert action.first.residue198 == action.last.residue198 == 40
        assert action.first.center == (3, 4)
        assert action.last.center == (5, 4)
        assert not action.observed_joint_endpoint_return
