"""Source-guarded carry-to-phase reuse, no all-future Q19 period assumptions."""

from __future__ import annotations

from random import Random

import pytest

from number_compiler.sequences.reverse_add.q19_authenticated_carry_phase import (
    AuthenticatedFiveCarryWindow,
)
from number_compiler.sequences.reverse_add.q19_repeat_port import Q19RepeatPortState
from number_compiler.sequences.reverse_add.temporal_boolean_ring_2_11 import (
    BCDPlanes,
    Powered211CarrySheets,
)


def _carries(x: int, width: int) -> tuple[int, int, int]:
    return BCDPlanes.from_residue(x, width).planes[1:]


def test_single_carry_plus_dyadic_residue_inverts_every_small_decimal_band() -> None:
    for width in (1, 2, 3):
        for x in range(10**width):
            w = AuthenticatedFiveCarryWindow.from_carries(
                _carries(x, width), width, x % (1 << width)
            )
            assert w.residue() == x
            assert w.bcd_planes == BCDPlanes.from_residue(x, width).planes


def test_random_authenticated_carries_reconstruct_q19_without_digit_tuple() -> None:
    rng = Random(19611)
    for width in (1, 3, 7, 19, 64, 127):
        for _ in range(30):
            x = rng.randrange(1, 10**width)
            band = AuthenticatedFiveCarryWindow.from_carries(
                _carries(x, width), width, x % (1 << width)
            )
            assert band.residue() == x
            source = tuple(int(ch) for ch in str(x)[::-1])
            expected = Q19RepeatPortState.from_digits(source)
            assert band.q19_repeat_state() == expected
            assert band.q19_repeat_state().advance() == expected.advance()


def test_same_carries_but_different_2adic_phase_cannot_be_reused() -> None:
    left = AuthenticatedFiveCarryWindow.from_carries(_carries(12, 2), 2, 12 % 4)
    right = AuthenticatedFiveCarryWindow.from_carries(_carries(13, 2), 2, 13 % 4)
    assert left.carries == right.carries
    assert left.parity_plane != right.parity_plane
    assert left.residue() == 12 and right.residue() == 13
    assert left.same_source_mask(right) == 0b10  # tens digit is unchanged


def test_exact_unmodified_positions_from_both_authenticated_sources() -> None:
    rng = Random(2026)
    for width in (1, 6, 40):
        for _ in range(100):
            x, y = rng.randrange(10**width), rng.randrange(10**width)
            a = AuthenticatedFiveCarryWindow.from_carries(
                _carries(x, width), width, x % (1 << width)
            )
            b = AuthenticatedFiveCarryWindow.from_carries(
                _carries(y, width), width, y % (1 << width)
            )
            expected = sum(
                (int((x // 10**j) % 10) == int((y // 10**j) % 10)) << j
                for j in range(width)
            )
            assert a.same_source_mask(b) == expected


def test_homogeneous_stage_accepts_only_its_own_carry_phase() -> None:
    rng = Random(211)
    for width in (1, 2, 3, 8, 17, 30):
        for _ in range(22):
            seed, q, g = (
                rng.randrange(10**width),
                rng.randrange(600),
                rng.randrange(600),
            )
            existing = Powered211CarrySheets.from_seed(seed, q, g, width)
            actual = _carries(existing.source.residue(), width)
            carried = Powered211CarrySheets.from_five_carry_sheet(
                seed, q, g, width, actual
            )
            assert carried == existing
            assert carried.source.planes == existing.source.planes
            assert carried.carry_eleven == existing.carry_eleven
            if existing.source.residue():
                assert (
                    carried.q19_next_with_repeats() == existing.q19_next_with_repeats()
                )


def test_unsafe_sheet_and_bad_carry_columns_are_rejected() -> None:
    with pytest.raises(ValueError, match="0..4"):
        AuthenticatedFiveCarryWindow.from_carries((1, 0, 1), 2, 0)
    with pytest.raises(ValueError, match="bounded"):
        AuthenticatedFiveCarryWindow.from_carries((0, 0, 4), 2, 0)
    with pytest.raises(ValueError, match="dyadic"):
        AuthenticatedFiveCarryWindow.from_carries((0, 0, 0), 2, 4)
    with pytest.raises(ValueError, match="does not belong"):
        Powered211CarrySheets.from_five_carry_sheet(196, 9, 11, 7, _carries(1234567, 7))


def test_phase_return_uses_exact_stage_owner_and_memoized_q19_action(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    stage = Powered211CarrySheets.from_seed(196, 1000, 1000, 16)
    first = stage.q19_next_with_repeats()
    period = stage.phase.phase_period_after_saturation()
    returned = stage.power(period, period)
    assert returned is stage

    def reject_eager_reconstruction(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("cached source-bound Q19 action was reconstructed")

    monkeypatch.setattr(Q19RepeatPortState, "advance", reject_eager_reconstruction)
    assert returned.q19_next_with_repeats() is first
    assert returned.q19_next_with_repeats()[0] == first[0]
    assert returned.q19_next() is first[0]


def test_supplied_carry_sheet_produces_same_q19_action() -> None:
    stage = Powered211CarrySheets.from_seed(196, 7, 9, 12)
    carried = Powered211CarrySheets.from_five_carry_sheet(
        196, 7, 9, 12, stage.source.planes[1:]
    )
    assert carried.q19_next_with_repeats() == stage.q19_next_with_repeats()


def test_consecutive_homogeneous_phase_reuse_mask_matches_physical_digit_positions() -> (
    None
):
    # Partial digit repetition across adjacent exponent generations is useful
    # only when the *source* phases are independently authenticated.
    for width in (4, 8, 18, 41):
        for q, g in ((0, 0), (width, width), (width + 4, 300), (100, 100)):
            before = Powered211CarrySheets.from_seed(196, q, g, width)
            after = before.power(1, 1)
            a = AuthenticatedFiveCarryWindow.from_mixed211_source(
                196, before.phase, before.source.planes[1:]
            )
            b = AuthenticatedFiveCarryWindow.from_mixed211_source(
                196, after.phase, after.source.planes[1:]
            )
            expected = sum(
                (before.source.digits_lsd()[j] == after.source.digits_lsd()[j]) << j
                for j in range(width)
            )
            assert a.same_source_mask(b) == expected
            # These are homogeneous source windows, not consecutive physical
            # seed-196 reverse/add states; no Q19 period is inferred.


def test_cross_width_single_sheet_lift_preserves_previous_digits() -> None:
    for width in (1, 2, 3, 5, 16, 32):
        for x in (0, 1, 12, 196, 10 ** (width + 1) - 1):
            lower = x % (10**width)
            upper = x % (10 ** (width + 1))
            a = AuthenticatedFiveCarryWindow.from_carries(
                _carries(lower, width), width, lower % (1 << width)
            )
            b = AuthenticatedFiveCarryWindow.from_carries(
                _carries(upper, width + 1), width + 1, upper % (1 << (width + 1))
            )
            mask = (1 << width) - 1
            assert (b.parity_plane & mask) == a.parity_plane
            assert tuple(p & mask for p in b.carries) == a.carries
            assert b.residue() % (10**width) == lower


def test_supplied_carry_path_never_requests_reconstructed_two_five_sheet(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    existing = Powered211CarrySheets.from_seed(196, 73, 129, 24)
    expected = existing.q19_next_with_repeats()
    carried = Powered211CarrySheets.from_five_carry_sheet(
        196, 73, 129, 24, existing.source.planes[1:]
    )

    def reject_old_double_decode(*_args: object, **_kwargs: object) -> None:
        raise AssertionError(
            "authenticated single-carry path repeated the old source decoder"
        )

    monkeypatch.setattr(
        BCDPlanes, "two_five_complementary_sheets", reject_old_double_decode
    )
    assert carried.q19_next_with_repeats() == expected
    assert carried.q19_next() == expected[0]
