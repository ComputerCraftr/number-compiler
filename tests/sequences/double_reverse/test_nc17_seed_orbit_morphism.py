"""Seed-specific NC17 full-word temporal morphism / outer-inner join."""

from __future__ import annotations

from collections.abc import Callable
from copy import copy
from dataclasses import replace
from math import comb
from typing import Never, TypeVar

import pytest

from number_compiler.arithmetic.automata.decimal_mod70_word import (
    DecimalMod70WordSummary,
)
from number_compiler.arithmetic.automata.pascal_word_moments import PascalWordMoments
from number_compiler.arithmetic.automata.slp_interval import SLPNodeArena, fold_slp_dag
from number_compiler.sequences.double_reverse import temporal_seed_morphism
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
    certified_seed_orbit_morphism,
    double_reverse_two_tick_mod70_action,
    square_seed_orbit_morphism,
    word_fiber_from_root,
)
from tests.sequences.double_reverse.packet_helpers import (
    integer_field,
    object_list,
    object_mapping,
)
from tests.support.decimal_mod70_oracle import (
    literal_mod70_packet as _literal_mod70_packet,
)
from tests.support.reverse_add_source_data import iterate_double_reverse

_Summary = TypeVar("_Summary")


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


def test_seed_word_fiber_folds_nested_msb_pascal_bands_from_same_slp() -> None:
    levels = (1, 2, 4)
    order = 3
    with DoubleReverseTerm(196, 24, max_state_bits=16384) as term:
        _owner, source = term.prepare_bank_source(max_prefix=24)
        fiber = word_fiber_from_root(
            source.arena,
            source.ledger,
            source.scratch_owner,
            source.root,
            pascal_levels=levels,
            pascal_order=order,
        )
        word = tuple(map(int, str(iterate_double_reverse(196, source.physical_prefix))))
        assert fiber.pascal_order == order
        assert fiber.pascal_levels == levels
        assert fiber.center_width == len(fiber.center)
        assert len(fiber.pascal_bands) == len(levels)
        for (level, summary), requested in zip(fiber.pascal_bands, levels, strict=True):
            cut = len(word) * ((1 << requested) - 1) // (2 << requested)
            literal_band = word[cut : len(word) - cut]
            expected_digits = tuple(
                sum(
                    (-1 if index & 1 else 1) * comb(index, degree) * digit
                    for index, digit in enumerate(literal_band)
                )
                % 11
                for degree in range(order + 1)
            )
            expected_markers = tuple(
                sum(
                    (-1 if index & 1 else 1) * comb(index, degree) * int(digit >= 5)
                    for index, digit in enumerate(literal_band)
                )
                % 11
                for degree in range(order + 1)
            )
            assert level == requested
            assert summary.length == len(literal_band)
            assert summary.digit_moments == expected_digits
            assert summary.marker_moments == expected_markers
            assert summary.first_marker == int(literal_band[0] >= 5)
            assert summary.last_marker == int(literal_band[-1] >= 5)


def test_source_join_does_not_treat_pascal_demand_as_word_authority() -> None:
    with DoubleReverseTerm(196, 24, max_state_bits=16384) as term:
        _owner, source = term.prepare_bank_source(max_prefix=24)
        plain = certified_seed_orbit_morphism(source, steps=2)
        rich = certified_seed_orbit_morphism(
            source,
            start_f_steps=2,
            steps=2,
            known_previous=plain,
            pascal_levels=(1, 2),
            pascal_order=3,
        )
        assert rich.first.root == plain.last.root
        assert rich.first.pascal_levels == (1, 2)
        assert rich.first.pascal_order == 3
        composed = plain.then(rich)
        assert composed.first.pascal_levels == ()
        assert composed.last.pascal_levels == (1, 2)
        assert composed.physical_interval == (16, 24)


def test_pascal_bands_and_residues_share_one_dag_fold(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = fold_slp_dag
    calls = 0

    def counted(
        arena: SLPNodeArena,
        root: int,
        *,
        empty_value: _Summary,
        terminal_value: Callable[[int], _Summary],
        concatenate: Callable[[_Summary, _Summary], _Summary],
        repeat: Callable[[_Summary, int], _Summary],
    ) -> dict[int, _Summary]:
        nonlocal calls
        calls += 1
        return original(
            arena,
            root,
            empty_value=empty_value,
            terminal_value=terminal_value,
            concatenate=concatenate,
            repeat=repeat,
        )

    with DoubleReverseTerm(196, 24) as term:
        _, source = term.prepare_bank_source(max_prefix=24)
        monkeypatch.setattr(temporal_seed_morphism, "fold_slp_dag", counted)
        fiber = word_fiber_from_root(
            source.arena,
            source.ledger,
            source.scratch_owner,
            source.root,
            pascal_levels=(1, 2, 3),
            mod70_projection=True,
        )
        assert len(fiber.pascal_bands) == 3
        assert fiber.mod70 is not None
        assert len(fiber.mod70_bands) == 3
        assert calls == 1
        source_word = str(iterate_double_reverse(196, source.physical_prefix))
        assert fiber.mod70.packet() == _literal_mod70_packet(source_word)
        for (level, _summary), (mod70_level, mod70_summary) in zip(
            fiber.pascal_bands, fiber.mod70_bands, strict=True
        ):
            assert level == mod70_level
            cut = len(source_word) * ((1 << level) - 1) // (2 << level)
            assert mod70_summary.packet() == _literal_mod70_packet(
                source_word[cut : len(source_word) - cut]
            )


def test_source_t_squared_mod70_affine_matches_independent_literal_endpoint() -> None:
    with DoubleReverseTerm(196, 40) as term:
        _owner, source = term.prepare_bank_source(max_prefix=24)
        source_word = str(iterate_double_reverse(196, source.physical_prefix))
        assert source_word[-1] != "0"
        morphism = certified_seed_orbit_morphism(
            source,
            steps=source.f_steps,
            mod70_projection=True,
        )
        source_summary = morphism.first.mod70
        assert source_summary is not None
        assert source_summary.packet() == _literal_mod70_packet(source_word)
        affine = morphism.source_t_squared_mod70_affine()
        projected = affine.apply(
            source_summary.word_mod70,
            multiply=lambda left, right: left * right % 70,
            add=lambda left, right: (left + right) % 70,
        )
        assert projected == iterate_double_reverse(196, source.physical_prefix + 2) % 70
        assert affine.multiplier in (4, 40)
        assert morphism.first.root == source.root


def test_source_t_squared_rejects_mutated_nested_mod70_summary() -> None:
    with DoubleReverseTerm(196, 40) as term:
        _owner, source = term.prepare_bank_source(max_prefix=24)
        morphism = certified_seed_orbit_morphism(
            source, steps=source.f_steps, mod70_projection=True
        )
        summary = morphism.first.mod70
        assert summary is not None
        admitted = morphism.source_t_squared_mod70_affine()
        original = summary.word_mod7
        try:
            object.__setattr__(summary, "word_mod7", (original + 1) % 7)
            with pytest.raises(ValueError, match="authority"):
                morphism.source_t_squared_mod70_affine()
        finally:
            object.__setattr__(summary, "word_mod7", original)
        assert morphism.source_t_squared_mod70_affine() == admitted
    with pytest.raises(ValueError, match="authority"):
        morphism.source_t_squared_mod70_affine()


@pytest.mark.parametrize("value", (1, 5, 52, 94, 101, 112, 159, 196, 589, 594))
def test_two_tick_mod70_carry_law_covers_both_growth_branches(value: int) -> None:
    summary = DecimalMod70WordSummary.identity()
    for digit in map(int, str(value)):
        summary = summary.then(DecimalMod70WordSummary.digit(digit))
    action = double_reverse_two_tick_mod70_action(summary)
    endpoint = iterate_double_reverse(value, 2)
    assert (
        action.apply(
            value % 70,
            multiply=lambda left, right: left * right % 70,
            add=lambda left, right: (left + right) % 70,
        )
        == endpoint % 70
    )
    assert action.multiplier == (4 if value % 10 < 5 else 40)


def test_two_tick_mod70_carry_law_rejects_width_normalizing_sources() -> None:
    for digits in ((3, 0), (0, 5)):
        summary = DecimalMod70WordSummary.identity()
        for digit in digits:
            summary = summary.then(DecimalMod70WordSummary.digit(digit))
        with pytest.raises(ValueError):
            double_reverse_two_tick_mod70_action(summary)


def test_cli_period_drivers_publish_guarded_mod70_word_and_band_factors() -> None:
    from number_compiler.sequences.double_reverse.temporal_seed_cli import (
        seed_morphism_cli_packet,
    )

    with DoubleReverseTerm(196, 40) as term:
        packet = seed_morphism_cli_packet(
            term,
            period_samples=4,
            period_stride=1,
            period_depth=1,
            period_max_lag=3,
            period_drivers=True,
        )
        scan = object_mapping(packet["period_observations"])
        factor = object_mapping(scan["spatial_mod70_cyclotomic"])
        source_word = str(iterate_double_reverse(196, 16))
        target_word = str(iterate_double_reverse(196, 40))
        assert factor["source_generation"] == 16
        assert factor["target_generation"] == 40
        assert factor["source"] == _literal_mod70_packet(source_word)
        assert factor["target"] == _literal_mod70_packet(target_word)
        assert factor["scope"] == (
            "finite source-issued word projections; spatial factors do not "
            "establish a temporal period"
        )
        bands = object_list(factor["bands"])
        assert len(bands) == 1
        band = object_mapping(bands[0])
        cut = len(source_word) // 4
        assert band["level"] == 1
        assert band["source"] == _literal_mod70_packet(
            source_word[cut : len(source_word) - cut]
        )
        affine = object_mapping(factor["source_t_squared_affine_mod70"])
        assert affine["status"] == "available"
        assert affine["physical_ticks"] == 2
        assert affine["source_generation"] == 16
        assert affine["target_generation"] == 18
        assert integer_field(affine, "projected_t_squared_mod70") == (
            iterate_double_reverse(196, 18) % 70
        )


def test_ordinary_seed_morphism_does_not_construct_pascal_observers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbid_moments(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("unrequested Pascal moment construction")

    with DoubleReverseTerm(196, 24) as term:
        monkeypatch.setattr(PascalWordMoments, "empty", forbid_moments)
        monkeypatch.setattr(PascalWordMoments, "symbol", forbid_moments)
        monkeypatch.setattr(DecimalMod70WordSummary, "identity", forbid_moments)
        monkeypatch.setattr(DecimalMod70WordSummary, "digit", forbid_moments)
        action = term.temporal_seed_orbit_morphism(4)
        assert action.first.pascal_levels == ()
        assert action.last.pascal_levels == ()
        assert action.first.mod70 is None
        assert action.last.mod70 is None
        assert_fiber_matches_word(action.last, str(iterate_double_reverse(196, 24)))


def test_pascal_interval_failure_clears_retained_product_fold(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fail_cut(_width: int, _level: int) -> Never:
        raise RuntimeError("injected Pascal interval failure")

    with DoubleReverseTerm(196, 24) as term:
        _, source = term.prepare_bank_source(max_prefix=24)
        before = source.ledger.account_usage(source.scratch_owner)
        with monkeypatch.context() as patch:
            patch.setattr(temporal_seed_morphism, "_centered_band_cut", fail_cut)
            with pytest.raises(RuntimeError, match="Pascal interval") as captured:
                word_fiber_from_root(
                    source.arena,
                    source.ledger,
                    source.scratch_owner,
                    source.root,
                    pascal_levels=(1, 2),
                )
        traceback = captured.value.__traceback__
        while traceback is not None and (
            traceback.tb_frame.f_code.co_name != "word_fiber_from_root"
        ):
            traceback = traceback.tb_next
        assert traceback is not None
        assert traceback.tb_frame.f_locals["summaries"] == {}
        assert traceback.tb_frame.f_locals["band_values"] == []
        assert source.ledger.account_usage(source.scratch_owner) == before
        retry = word_fiber_from_root(
            source.arena,
            source.ledger,
            source.scratch_owner,
            source.root,
            pascal_levels=(1, 2),
        )
        assert len(retry.pascal_bands) == 2


def test_order_zero_pascal_demand_survives_source_temporal_squaring() -> None:
    with DoubleReverseTerm(196, 24, max_state_bits=16384) as term:
        _owner, source = term.prepare_bank_source(max_prefix=24)
        first = certified_seed_orbit_morphism(
            source,
            steps=2,
            pascal_levels=(1,),
            pascal_order=0,
        )
        squared = square_seed_orbit_morphism(source, first)
        assert squared.steps == 4
        assert squared.first.pascal_levels == (1,)
        assert squared.last.pascal_levels == (1,)
        assert squared.first.pascal_order == 0
        assert squared.last.pascal_order == 0


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
        assert (
            metrics["double_reverse_hashlife_cones"] > 0
            or metrics["double_reverse_packed_diagonal_row_evaluations"] > 0
        )
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
