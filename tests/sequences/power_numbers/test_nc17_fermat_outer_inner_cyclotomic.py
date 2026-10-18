"""NC17 source-bound mod99/100 × signed 2w temporal ring tests."""

from dataclasses import replace
from math import lcm
from unittest.mock import patch

import pytest

from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.three_power_outer_inner_cyclotomic import (
    OUTER_MODULUS,
    FermatOuterCyclotomicClock,
    UnknownBinaryBlockCongruence,
)
from tests.support.exact_integer_power import exact_integer_power


def test_exact_nonunit_99_100_clock_physical_and_dyadic() -> None:
    assert [
        FermatOuterCyclotomicClock.from_level(t).residue99 for t in range(1, 10)
    ] == [9, 81, 27, 36, 9, 81, 27, 36, 9]
    assert [
        FermatOuterCyclotomicClock.from_level(t).residue100 for t in range(2, 10)
    ] == [81, 61, 21, 41, 81, 61, 21, 41]
    assert [
        FermatOuterCyclotomicClock.from_level(t).residue9900 for t in range(2, 10)
    ] == [81, 6561, 1521, 6741, 81, 6561, 1521, 6741]
    for t in range(1, 19):
        clock = FermatOuterCyclotomicClock.from_level(t)
        assert clock.residue9900 == pow(3, 1 << t, OUTER_MODULUS)
        assert clock.residue198 == pow(3, 1 << t, 198)
        assert clock.dyadic_successor() == FermatOuterCyclotomicClock.from_level(t + 1)
        for physical in (0, 1, 2, 7, 19, 20, 21, 1001):
            moved = clock.advance(physical)
            assert moved.residue9900 == pow(3, (1 << t) + physical, OUTER_MODULUS)
            assert (
                moved.residue9900
                == clock.residue9900 * pow(3, physical, OUTER_MODULUS) % OUTER_MODULUS
            )
    with pytest.raises(ValueError):
        FermatOuterCyclotomicClock.from_level(0)
    with pytest.raises(ValueError):
        FermatOuterCyclotomicClock.from_level(3).advance(-1)
    with pytest.raises(ArithmeticError):
        replace(FermatOuterCyclotomicClock.from_level(3), residue99=9).verify()


def test_spatial_joint_period_uses_true_two_nonunit_head_exceptions() -> None:
    assert pow(2, 60, 9900) != 1
    for w in (4, 8, 16, 32):
        period = lcm(60, 2 * w)
        f = (1 << w) + 1
        for j in range(2, period + 12):
            assert pow(2, j + period, 9900) == pow(2, j, 9900)
            assert pow(2, j + period, f) == pow(2, j, f)
    assert pow(2, 1 + 60, 9900) != pow(2, 1, 9900)


def test_unknown_binary_block_rejects_malformed_coordinates() -> None:
    with pytest.raises(TypeError, match="exact integers"):
        UnknownBinaryBlockCongruence(True, 8, 0, 5)
    for coordinates in ((0, 0, 0, 5), (-1, 8, 0, 5), (0, 8, 0, 0), (0, 8, 5, 5)):
        with pytest.raises(ValueError, match="domain"):
            UnknownBinaryBlockCongruence(*coordinates)


def test_f4_source_block_congruence_and_full_reference_projection() -> None:
    joint = FermatNumberSpec(4).demand_three_power_source_restricted_phase(15)
    assert joint.producer_verified
    outer = joint.outer_inner
    assert outer.producer_verified
    assert (outer.phase_period, outer.fold_width) == (480, 16)
    assert outer.clock.residue9900 == pow(3, 1 << 15, 9900)
    assert outer.known_head_bits == (1, 0)
    assert not outer.unknown_head_positions
    assert outer.project_known_fold() == joint.phase.known_signed_fold
    assert outer.project_known_outer() == outer.known_source_residue9900
    assert (
        sum(outer.unknown_phase_capacities) == joint.phase.symbolic_unknown_site_count
    )
    assert (
        outer.required_unknown_residue9900
        == (outer.clock.residue9900 - outer.project_known_outer()) % 9900
    )
    forced = outer.forced_single_block
    assert forced is not None and forced.modulus == 2475
    x = 3 ** (1 << 15)  # REFERENCE-ONLY; never source production
    gap = (x >> forced.start) & ((1 << forced.width) - 1)
    assert gap % forced.modulus == forced.residue
    assert outer.verify_complete_fiber(x) == (x % 9900, x % 65537)
    assert not joint.source_to_global_fold_proven
    assert joint.terminal_status == "UNKNOWN"


def test_f5_unknown_middle_constrained_but_prime_bit_refused() -> None:
    joint = FermatNumberSpec(5).demand_three_power_source_restricted_phase(31)
    assert joint.producer_verified
    outer = joint.outer_inner
    assert outer.phase_period == 960
    assert outer.clock.residue99 == 27 and outer.clock.residue100 == 61
    assert outer.clock.residue9900 == pow(3, 1 << 31, 9900)
    assert outer.forced_single_block is not None
    assert (
        outer.forced_single_block.start,
        outer.forced_single_block.residue,
        outer.forced_single_block.modulus,
    ) == (64, 781, 2475)
    assert sum(outer.unknown_phase_capacities) == 3403680981
    assert joint.cylinder.combined_modulus == (1 << 64) * 5**6 * 99
    assert joint.cylinder.combined_residue % 9900 == outer.clock.residue9900
    assert outer.unknown_count_equation[1:] == (
        outer.required_unknown_residue9900,
        9900,
    )
    assert joint.cylinder.ingress_options(64) == (1,)
    assert joint.cylinder.ingress_options(65) == (0, 2)
    assert not joint.source_to_global_fold_proven
    assert joint.complete_signed_fold is None
    assert joint.terminal_status == "UNKNOWN"
    next_clock, symbolic_power = outer.physical_successor(1 << 31)
    assert symbolic_power == (3, 1 << 31)
    assert (
        next_clock.residue9900 == FermatOuterCyclotomicClock.from_level(32).residue9900
    )


def test_observer_alias_survives_even_full_mod99_100_join() -> None:
    joint = FermatNumberSpec(4).demand_three_power_source_restricted_phase(15)
    x = 3 ** (1 << 15)
    m = (1 << 64) * 5**6
    alt = x + 99 * m
    assert (alt - x) % 9900 == 0
    assert joint.cylinder._admitted(x) is not None
    assert joint.cylinder._admitted(alt) is not None
    assert (
        joint.outer_inner.verify_complete_fiber(alt)[0]
        == joint.outer_inner.clock.residue9900
    )
    assert x % 65537 == 65536
    assert alt % 65537 == 39523
    assert joint.terminal_status == "UNKNOWN"
    assert not joint.source_to_global_fold_proven


def test_tampering_source_bound_outer_phase_is_refused() -> None:
    joint = FermatNumberSpec(5).demand_three_power_source_restricted_phase(31)
    assert not replace(joint.outer_inner).producer_verified
    assert not replace(
        joint.outer_inner, required_unknown_residue9900=0
    ).producer_verified
    # The clock is derived from the authenticated source level, not a mutable
    # cache field. Even a separately issued source at another level cannot be
    # substituted into this cylinder without invalidating its seal.
    changed_source = FermatNumberSpec(5).demand_three_power_signed_border_action(
        joint.cylinder.source.level - 1
    )
    assert changed_source.producer_verified
    assert not replace(joint.cylinder, source=changed_source).producer_verified
    with pytest.raises(ValueError, match="unissued"):
        replace(joint.outer_inner).physical_successor(1)


def test_no_pepin_modular_squaring_in_joint_constructor() -> None:
    import builtins

    original = exact_integer_power
    candidate = (1 << 32) + 1

    def forbidden(base: int, exponent: int, modulus: int | None = None) -> int:
        if modulus == candidate and (base != 2 or exponent >= 64):
            raise AssertionError("Fermat candidate exponentiation is forbidden")
        if modulus is None:
            return original(base, exponent)
        return original(base, exponent, modulus)

    with patch.object(builtins, "pow", forbidden):
        join = FermatNumberSpec(5).demand_three_power_source_restricted_phase(31)
        assert join.outer_inner.producer_verified
        assert join.terminal_status == "UNKNOWN"


def test_terminal_source_demand_exposes_joint_issuer_without_prime_promotion() -> None:
    from number_compiler.sequences.power_numbers.terminal_source_demand import (
        SourceTerminalDemand,
    )

    demand = SourceTerminalDemand.for_candidate("fermat", 5)
    packets = demand.observe_fermat_outer_inner_cyclotomic()
    assert len(packets) == 5
    assert [p.clock.level for p in packets] == list(range(27, 32))
    assert all(p.producer_verified for p in packets)
    assert all(
        p.unknown_blocks and not p.all_signed_phase_counts_forced for p in packets
    )
    for p in packets:
        assert p.clock.residue9900 == pow(3, 1 << p.clock.level, 9900)


def test_source_wide_one_tripling_matches_physical_clock() -> None:
    c = FermatNumberSpec(2).demand_three_power_two_sided_source_cylinder(
        3,
        phase_binary_places=8,
        phase_decimal_places=2,
        low_binary_places=4,
        low_decimal_places=2,
        high_binary_places=4,
        high_decimal_places=2,
    )
    target = c.transported_target()
    assert target is not None and target.count == 1
    assert target.first == 3**9
    assert target.residue % 9900 == c.outer_clock.advance(1).residue9900
    assert target.modulus == 3 * c.combined_modulus
