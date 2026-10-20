"""Regression gates for the NC16 source-bound signed-3X border repair."""

from collections.abc import Callable
from dataclasses import replace
from typing import cast

import pytest

from number_compiler.arithmetic.carry.tripling_transfer import compose_transfer
from number_compiler.arithmetic.fields.three_power_radix import decimal_tripling_order
from number_compiler.sequences.power_numbers import (
    three_power_signed_border_action as signed_owner,
)
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
    CyclotomicTriplingClock,
    WeightedBinaryCarryBlock,
    exact_physical_carry_periods,
)

known_block = cast(
    Callable[[int, int, int], WeightedBinaryCarryBlock],
    object.__getattribute__(signed_owner, "_known_block"),
)
signed_position_factor = cast(
    Callable[[int, int], int],
    object.__getattribute__(signed_owner, "_signed_position_factor"),
)
unknown_block = cast(
    Callable[[int, int], WeightedBinaryCarryBlock],
    object.__getattribute__(signed_owner, "_unknown_block"),
)


def test_signed_position_uses_finite_clock_for_absolute_coordinates() -> None:
    for width in (1, 2, 7, 16):
        for position in range(4 * width + 1):
            assert signed_position_factor(position, width) == pow(
                2, position, (1 << width) + 1
            )
    huge = (1 << 65_535) + 23
    assert signed_position_factor(huge, 16) == signed_position_factor(huge % 32, 16)


def test_unknown_middle_relation_reuses_exact_orbit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import tripling_transfer

    original = tripling_transfer.compose_sets
    visits = 0

    def bounded_compose(
        left: frozenset[tripling_transfer.CarryFn],
        right: frozenset[tripling_transfer.CarryFn],
    ) -> frozenset[tripling_transfer.CarryFn]:
        nonlocal visits
        visits += 1
        assert visits <= 16
        return original(left, right)

    monkeypatch.setattr(tripling_transfer, "compose_sets", bounded_compose)
    width = (1 << 65_535) + 1
    for base in (2, 10):
        actual = tripling_transfer.unknown_middle_transfer_set(base, width)
        reference = frozenset((tripling_transfer.IDENTITY,))
        atoms = frozenset(
            tripling_transfer.digit_transfer(base, d) for d in range(base)
        )
        for _ in range(7):
            reference = original(reference, atoms)
        assert actual == reference


def test_physical_cyclotomic_clock_and_two_clocks_are_separate() -> None:
    for level in (2, 3, 14, 15, 30, 31):
        for depth in (2, 3, 6):
            clock = CyclotomicTriplingClock.from_dyadic_level(level, depth)
            clock.verify()
            mod = 10**depth
            assert clock.residue == pow(3, 1 << level, mod)
            a, b = 17, 1001
            assert clock.advance(a).advance(b) == clock.advance(a + b)
            assert clock.advance(1).residue == 3 * clock.residue % mod
            assert clock.dyadic_jump().residue == pow(3, 1 << (level + 1), mod)
            assert clock.carry_after(depth) == (3 * clock.residue) // mod
    assert decimal_tripling_order(4) == 500
    clock = CyclotomicTriplingClock.from_dyadic_level(2, 2)
    assert clock.residue == 81
    assert clock.advance(1).residue == 43
    assert clock.dyadic_jump().residue == 61
    with pytest.raises(ArithmeticError):
        replace(clock, phase=(clock.phase + 1) % clock.period).verify()


def test_all_source_physical_carry_harmonics_have_closed_cycles() -> None:
    expected = (4, 20, 100, 500, 5000, 50000)
    records = exact_physical_carry_periods(6)
    assert tuple(row[0] for row in records) == expected
    assert tuple(row[1] for row in records) == expected
    assert records[0][2] == 1
    assert records[0][3] == 4
    with pytest.raises(ValueError, match="budget"):
        exact_physical_carry_periods(6, max_states=1_000)


def test_weighted_actions_compose_without_collapsing_signed_word() -> None:
    for width in range(2, 12):
        for value in (0, 1, 3, (1 << width) // 3, (1 << width) - 1):
            whole = known_block(0, width, value)
            for split in range(1, width):
                a = known_block(0, split, value % (1 << split))
                b = known_block(split, width - split, value >> split)
                assert whole.transfers[0] == compose_transfer(
                    a.transfers[0], b.transfers[0]
                )
                for carry_in in (0, 1, 2):
                    first_out = a.possible_outgoing(carry_in)[0]
                    second_out = b.possible_outgoing(first_out)[0]
                    emitted = a.emitted_value(carry_in, first_out)
                    second_emitted = b.emitted_value(first_out, second_out)
                    assert emitted is not None and second_emitted is not None
                    emitted += second_emitted << split
                    assert emitted == whole.emitted_value(carry_in, second_out)
                    # A complete packet can be reconstructed from the two
                    # absolute-local H5 masks without assuming a middle H5=0.
                    h_a = a.emission_h5(carry_in, first_out)
                    h_b = b.emission_h5(first_out, second_out)
                    h_whole = whole.emission_h5(carry_in, second_out)
                    assert h_a is not None and h_b is not None and h_whole is not None
                    for j in (0, 1):
                        assert h_whole[j].phi2 == (h_a[j].phi2 + h_b[j].phi2) % 5
                        assert h_whole[j].phi3_a == (h_a[j].phi3_a + h_b[j].phi3_a) % 5
                        assert h_whole[j].phi3_b == (h_a[j].phi3_b + h_b[j].phi3_b) % 5


def test_h5_and_carry_collision_cannot_merge_distinct_signed_sources() -> None:
    a, b = known_block(0, 10, 7), known_block(0, 10, 56)
    assert a.transfers == b.transfers == ((0, 0, 0),)
    assert a.emission_h5(0, 0) == b.emission_h5(0, 0)
    assert a.signed_source(8) != b.signed_source(8)
    assert a.signed_output(0, 0, 8) != b.signed_output(0, 0, 8)
    unknown = unknown_block(1000, 10**9)
    assert unknown.emitted_value(0, 0) is None
    assert unknown.emission_h5(0, 0) is None
    with pytest.raises(ValueError, match="refused"):
        unknown.emitted_value(0, 9)


def test_complete_small_source_checks_signed_weights_and_overflow() -> None:
    packet = FermatNumberSpec(2).demand_three_power_signed_border_action(
        2,
        phase_binary_places=4,
        phase_decimal_places=1,
        low_binary_places=3,
        high_binary_places=4,
        low_decimal_places=1,
        high_decimal_places=1,
    )
    assert packet.producer_verified and packet.full_source_fold_proven
    assert packet.complete_tripling_fold() == (81 % 17, 243 % 17)
    assert not packet.unknown_blocks
    assert packet.terminal_status == "UNKNOWN"  # 3X is NOT a Pépin proof
    assert packet.physical_decimal_clock().residue == 1
    assert packet.signed_leading_overflow_options()


def test_f4_f5_two_sided_carries_and_unknown_signed_terms() -> None:
    for index, level in ((4, 14), (4, 15), (5, 30), (5, 31)):
        packet = FermatNumberSpec(index).demand_three_power_signed_border_action(level)
        assert packet.producer_verified and packet.leading_resets_carry
        assert packet.terminal_status == "UNKNOWN"
        assert not packet.full_source_fold_proven
        assert len(packet.unknown_blocks) >= 1
        assert packet.unresolved_signed_variables()
        assert any(block.width > 1000 for block in packet.unknown_blocks)
        assert packet.origin.binary_phase_bank is not None
        clock = packet.physical_decimal_clock()
        assert packet.origin.decimal_phase_bank is not None
        assert clock.residue == packet.origin.decimal_phase_bank.source_prefix
        assert clock.carry_vector() == packet.origin.decimal_phase_bank.carry_vector
        assert packet.conditional_signed_ports()
        with pytest.raises(ValueError, match="symbolic middle"):
            packet.complete_tripling_fold()
    packet = FermatNumberSpec(5).demand_three_power_signed_border_action(31)
    # Both ingress 0 and 1 lead to the same upper carry, but the signed
    # output words differ by one; carry RESET must not collapse the emissions.
    leading = packet.blocks[-1]
    high_edges = packet.admissible_edges[-1]
    assert (0, 2) in high_edges and (1, 2) in high_edges
    low_emitted = leading.emitted_value(0, 2)
    assert low_emitted is not None
    assert leading.emitted_value(1, 2) == low_emitted + 1
    assert leading.signed_output(1, 2, 32) != leading.signed_output(0, 2, 32)


def test_certified_dyadic_endpoint_power_does_not_materialize_complete_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.power_numbers.three_dyadic_boolean_counter as counter

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("no eager candidate-ring square in the source quotient")

    monkeypatch.setattr(counter, "demand_bounded_complete_unit_certificate", forbidden)
    monkeypatch.setattr(counter, "demand_bounded_fermat_counter_certificate", forbidden)
    packet = FermatNumberSpec(4).demand_three_power_signed_border_action(14)
    assert packet.demanded_dyadic_endpoint(1).level == 15
    assert (
        packet.demanded_dyadic_endpoint(1).physical_decimal_clock().residue % 100 == 61
    )
    packet5 = FermatNumberSpec(5).demand_three_power_signed_border_action(30)
    assert packet5.demanded_dyadic_endpoint(1).level == 31
    with pytest.raises(ValueError, match="horizon"):
        packet5.demanded_dyadic_endpoint(2)
    # The actual terminal demand consumes the same source-grounded producer.
    demands = (
        FermatNumberSpec(4)
        .terminal_source_demand()
        .observe_fermat_signed_border_actions()
    )
    assert tuple(p.level for p in demands) == tuple(range(11, 16))
    assert all(p.producer_verified and p.terminal_status == "UNKNOWN" for p in demands)
    assert any(p.unknown_blocks for p in demands)


def test_issuer_rejects_tampered_weighted_action() -> None:
    packet = FermatNumberSpec(4).demand_three_power_signed_border_action(14)
    bad = replace(packet, admissible_edges=(((0, 2),),) + packet.admissible_edges[1:])
    assert not bad.producer_verified
    with pytest.raises(ValueError, match="unissued"):
        bad.conditional_signed_ports()


def test_weighted_block_rejects_false_carry_and_unbounded_fold() -> None:
    block = known_block(0, 10, 7)
    with pytest.raises(ValueError, match="disagrees"):
        replace(block, transfers=((2, 2, 2),))
    with pytest.raises(ValueError, match="budget"):
        block.signed_output(0, 0, 10**30)
    with pytest.raises(ValueError, match="ingress"):
        block.emitted_value(True, 0)
    with pytest.raises(ValueError, match="source word"):
        known_block(0, 10**30, 7)


def test_invalid_windows_refuse_before_radial_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import (
        three_power_bilateral_border as owner,
    )

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("malformed windows must refuse before source construction")

    monkeypatch.setattr(owner, "demand_three_power_bilateral_quotient", forbidden)
    with pytest.raises(ValueError, match="source-window"):
        owner.demand_three_power_bilateral_interior(
            4, 14, binary_windows=((12, 1),) * 10
        )
    with pytest.raises(ValueError, match="phase depth"):
        owner.demand_three_power_bilateral_interior(4, 14, phase_binary_places=10**30)
