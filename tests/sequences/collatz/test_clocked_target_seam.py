from __future__ import annotations

from collections import defaultdict
from random import Random

import pytest

from number_compiler.sequences.collatz.clocked_target_seam import (
    ClockedTargetSeamArena,
)
from number_compiler.sequences.collatz.inverse_three_clock import (
    InverseThreeClock,
    NormalizedCylinderJet,
    radix64_clocked_tangent,
    radix64_cylinder_views,
)
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz


def _advance(value: int, events: int) -> int:
    for _ in range(events):
        value = accelerated_odd_collatz(value).target
    return value


def test_occupancy_curvature_is_exactly_the_existing_seven_way_skeleton() -> None:
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


def test_normalized_affine_cylinders_compose_with_identity_hasse_jet() -> None:
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


def test_a1_clocked_target_seam_counts_and_discards_transition_provenance() -> None:
    for bits, expected in ((14, 6_144), (16, 24_576)):
        arena = ClockedTargetSeamArena()
        source_count = 1 << (bits - 1)
        for source in range(1, 1 << bits, 2):
            target = accelerated_odd_collatz(source).target
            seam = arena.publish(accelerated_tick=1, target=target)
            assert seam.target == target
            assert seam.clock(18).phase == 1
        assert arena.requests == source_count
        assert arena.retained_seams == expected
        assert arena.cache_hits == source_count - expected


def test_every_odd14_a1_alias_has_one_exact_future_at_all_checked_depths() -> None:
    fibers: dict[tuple[object, ...], list[int]] = defaultdict(list)
    arena = ClockedTargetSeamArena()
    for source in range(1, 1 << 14, 2):
        target = accelerated_odd_collatz(source).target
        seam = arena.publish(accelerated_tick=1, target=target)
        fibers[seam.canonical_key].append(source)
    for sources in fibers.values():
        if len(sources) < 2:
            continue
        target = accelerated_odd_collatz(sources[0]).target
        assert all(
            accelerated_odd_collatz(source).target == target for source in sources
        )
        for future in (1, 2, 4, 8, 12):
            assert len({_advance(target, future) for _source in sources}) == 1


def test_exact_tick_is_not_replaced_by_a_fixed_precision_phase() -> None:
    arena = ClockedTargetSeamArena()
    early = arena.publish(accelerated_tick=1, target=17)
    late = arena.publish(accelerated_tick=17, target=17)
    assert early.clock(6) == late.clock(6)
    assert early != late
    assert early.clock(12) != late.clock(12)


def test_clocked_target_seam_budget_is_outside_identity() -> None:
    arena = ClockedTargetSeamArena(max_entries=1)
    first = arena.publish(accelerated_tick=1, target=17)
    assert arena.publish(accelerated_tick=1, target=17) is first
    assert arena.cache_hits == 1
    with pytest.raises(ValueError, match="budget exceeded"):
        arena.publish(accelerated_tick=2, target=13)
    assert arena.retained_seams == 1
