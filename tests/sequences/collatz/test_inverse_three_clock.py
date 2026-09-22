from __future__ import annotations

from collections import Counter
from collections.abc import Callable
from random import Random
from typing import cast

import pytest

from number_compiler.arithmetic.carry.collatz_output_quotient import radix64_domain
from number_compiler.arithmetic.fields.two_adic import v2_nonzero
from number_compiler.sequences.collatz.inverse_three_clock import (
    ClockedTangentArena,
    InverseThreeClock,
    NormalizedCylinderJet,
    Radix64CylinderViews,
    inverse_three_root_cylinder,
    radix64_clocked_tangent,
    radix64_cylinder_views,
)
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz


def test_clocked_occupancy_curvature_refines_tangent_skeleton() -> None:
    for phase in range(16):
        clock = InverseThreeClock(6, phase)
        for digit in range(64):
            views = radix64_cylinder_views(clock, digit)
            occupancy = views.occupancy
            assert occupancy[0] == 1
            assert tuple(sorted(occupancy, reverse=True)) == occupancy
            assert sum(views.curvature) == int(not views.skeleton.match)
            assert views.skeleton == radix64_clocked_tangent(clock, digit).skeleton
            assert views.branch_scale == (
                1 if views.skeleton.match else 1 << (6 - views.skeleton.valuation_bits)
            )


def test_normalized_cylinder_composition_preserves_hasse_jet() -> None:
    rng = Random(0xC011A72)
    for _ in range(2_500):
        k1, k2 = rng.randrange(7), rng.randrange(7)
        target = rng.randrange(1, 1 << 16)
        a2 = rng.randrange(1 << k2)
        middle = (target << k2) - a2
        a1 = rng.randrange(1 << k1)
        source = (middle << k1) - a1
        first = NormalizedCylinderJet(1, k1, a1)
        second = NormalizedCylinderJet(1, k2, a2)
        composed = first.then(second)
        assert first.apply_exact(source) == middle
        assert second.apply_exact(middle) == target
        assert composed.apply_exact(source) == target
        assert composed.innovation == a1 + (a2 << k1)
        assert composed.normalized_hasse_jet == (0, 1)
        stride = 1 << composed.valuation
        images = tuple(composed.apply_exact(source + j * stride) for j in range(3))
        assert images == (target, target + 1, target + 2)
        assert images[2] - 2 * images[1] + images[0] == 0


def test_inverse_three_clock_is_a_prefix_local_bijection() -> None:
    for precision in range(3, 13):
        modulus = 1 << precision
        period = 1 << (precision - 2)
        for phase in range(2 * period):
            clock = InverseThreeClock(precision, phase)
            assert clock.phase == phase % period
            assert (
                clock.canonical_key
                == InverseThreeClock(precision, phase + 5 * period).canonical_key
            )
            source = (37 * phase + 11) % modulus
            normalized = clock.normalized_prefix(source)
            assert clock.recover_prefix(normalized) == source
            assert normalized == source * pow(3, -phase, modulus) % modulus


def test_all_1024_low_contexts_have_exactly_seven_tangent_skeletons() -> None:
    arena = ClockedTangentArena()
    skeletons: Counter[tuple[object, ...]] = Counter()
    carry_domains_by_skeleton: dict[tuple[object, ...], set[int]] = {}
    for phase in range(16):
        clock = InverseThreeClock(6, phase)
        root = clock.root
        for digit in range(64):
            occurrence = arena.compile(clock, digit)
            key = occurrence.skeleton.canonical_key
            skeletons[key] += 1
            difference = digit - root
            if difference:
                assert occurrence.skeleton.valuation_bits == v2_nonzero(difference)
                assert occurrence.odd_payload == difference >> v2_nonzero(difference)
            else:
                assert occurrence.skeleton.match
                assert occurrence.apply_higher(12345) == 12345
            for higher in (0, 1, 17):
                if difference:
                    expected = (difference + 64 * higher) >> v2_nonzero(difference)
                    assert occurrence.apply_higher(higher) == expected
            domain = radix64_domain(digit)
            carry_domains_by_skeleton.setdefault(key, set()).add(domain)
    assert sum(skeletons.values()) == 1024
    assert len(skeletons) == 7
    assert arena.retained_skeletons == 7
    assert arena.requests == 1024
    assert arena.cache_hits == 1017
    assert {key[-1] for key in skeletons if not key[-2]} == set(range(6))
    for key, domains in carry_domains_by_skeleton.items():
        if not key[-2]:
            assert len(domains) >= 3


def test_low_consumer_does_not_evaluate_the_full_precision_root(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    clock = InverseThreeClock(16_000, 11)

    def forbidden(_self: object) -> int:
        raise AssertionError("radix-64 consumer evaluated the full root")

    monkeypatch.setattr(InverseThreeClock, "root", property(forbidden))
    arena = ClockedTangentArena()
    tangent = arena.compile(clock, 17)
    root_digit = -pow(3, -11, 64) % 64
    difference = 17 - root_digit
    assert tangent.skeleton.valuation_bits == v2_nonzero(difference)
    assert tangent.odd_payload == difference >> v2_nonzero(difference)


def test_low_consumer_does_not_materialize_derived_view_rows(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(_self: object) -> tuple[int, ...]:
        raise AssertionError("consumer materialized a derived occupancy row")

    monkeypatch.setattr(Radix64CylinderViews, "occupancy", property(forbidden))
    monkeypatch.setattr(Radix64CylinderViews, "curvature", property(forbidden))
    arena = ClockedTangentArena()
    for phase in range(16):
        clock = InverseThreeClock(6, phase)
        for digit in range(64):
            tangent = arena.compile(clock, digit)
            difference = digit - clock.root
            expected = 6 if difference == 0 else v2_nonzero(difference)
            assert tangent.skeleton.valuation_bits == expected
    assert arena.retained_skeletons == 7


@pytest.mark.parametrize("precision", range(6, 15))
def test_root_lift_is_affine_in_the_next_temporal_phase_digit(
    precision: int,
) -> None:
    period = 1 << (precision - 2)
    for phase in range(period):
        clock = InverseThreeClock(precision, phase)
        assert clock.lift_coefficient == (35 if precision == 6 else 3)
        for digit in range(64):
            lifted = clock.lift_phase_digit(digit)
            assert lifted.root & ((1 << precision) - 1) == clock.root
            assert (lifted.root >> precision) & 63 == clock.lifted_root_digit(digit)


def test_phase_bits_at_or_above_precision_minus_two_are_invisible() -> None:
    for precision in range(3, 17):
        clock = InverseThreeClock(precision, 19)
        for level in range(precision - 2, precision + 4):
            assert InverseThreeClock(precision, clock.phase + (1 << level)) == clock


def test_clock_projects_to_existing_hensel_cylinder_owner() -> None:
    for precision in (6, 12, 18):
        for phase in range(16):
            clock = InverseThreeClock(precision, phase)
            cylinder = inverse_three_root_cylinder(clock)
            assert cylinder.bits == precision
            assert cylinder.residue == -pow(3, -phase, 1 << precision) % (
                1 << precision
            )


def test_tangent_reconstructs_signed_full_source_root_displacement() -> None:
    for phase in range(16):
        clock = InverseThreeClock(12, phase)
        root = clock.root
        for source in range(1 << 10):
            tangent = radix64_clocked_tangent(clock, source & 63)
            higher = (source >> 6) - (root >> 6)
            valuation = tangent.skeleton.valuation_bits
            assert tangent.apply_higher(higher) == (source - root) >> valuation


def test_finite_normalized_window_is_not_exact_successor_complete() -> None:
    clock = InverseThreeClock(12, 0)
    left, right = 1, 1 + (1 << 12)
    assert clock.normalized_prefix(left) == clock.normalized_prefix(right)
    assert accelerated_odd_collatz(left).target == 1
    assert accelerated_odd_collatz(right).target == 3073


def test_helix_children_share_one_base_root(monkeypatch: pytest.MonkeyPatch) -> None:
    original = cast(
        Callable[[InverseThreeClock], int], InverseThreeClock.__dict__["root"].fget
    )
    calls = 0

    def counted(clock: InverseThreeClock) -> int:
        nonlocal calls
        calls += 1
        assert original is not None
        return original(clock)

    monkeypatch.setattr(InverseThreeClock, "root", property(counted))
    for q in (6, 7, 12, 18, 30):
        clock = InverseThreeClock(q, 12345)
        key = clock.canonical_key
        before = calls
        centered = [clock.centered_lift_digit(a) for a in range(64)]
        assert len(set(centered)) == 64
        assert calls == before
        digits = [clock.lifted_root_digit(a) for a in range(64)]
        assert calls == before + 1
        modulus = 1 << (q + 6)
        assert digits == [
            (-pow(3, -(clock.phase + a * clock.period), modulus) % modulus) >> q
            for a in range(64)
        ]
        assert clock.canonical_key == key
        assert clock == InverseThreeClock(q, 12345)
