"""Exact NC14 joined-source tests; no prime-bit or recurrence oracles in runtime."""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

import pytest

from number_compiler.arithmetic.fields.walsh import walsh64, walsh64_mod5
from number_compiler.sequences.power_numbers import source_matrix
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.source_matrix import SmallModulusWork
from number_compiler.sequences.power_numbers.three_power_joint_quotient import (
    DEFAULT_RADIX_DEMANDS,
    SourceWalsh64,
    WalshH5,
    _join_crt,
    _normalized_unit_residue,
    demand_three_power_joint_quotient,
)


def test_radix_powers_use_one_source_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    called: list[tuple[str, int, int]] = []
    original = source_matrix.source_residue

    def spy(family: str, level: int, modulus: int) -> tuple[int, SmallModulusWork]:
        called.append((family, level, modulus))
        return original(family, level, modulus)

    monkeypatch.setattr(source_matrix, "source_residue", spy)
    t = 15
    for base, places in ((2, 12), (5, 6), (7, 5), (10, 5), (27, 4)):
        output = FermatNumberSpec(4).demand_three_power_multiradix_port(t, base, places)
        modulus = base**places
        assert called[-1] == ("fermat", t - 1, modulus)
        assert output.previous_residue == pow(3, 1 << (t - 1), modulus)
        assert output.source_residue == pow(3, 1 << t, modulus)
        assert output.next_residue == pow(3, 1 << (t + 1), modulus)
        assert output.work[0].scalar_power_compositions == 1
        assert output.work[2].scalar_power_compositions == 1
    assert len(called) == 5


def test_normalized_unit_matches_integer_division_and_odd_inverse() -> None:
    for level in range(1, 10):
        x = 3 ** (1 << level)
        u = (x - 1) >> (level + 2)
        for modulus in (2, 4, 8, 16, 32, 64, 3, 9, 27, 5, 125, 7, 49, 10, 100, 1000):
            assert _normalized_unit_residue(level, modulus, x % modulus) == u % modulus


def test_joined_crt_matches_complete_integer_source_bounded() -> None:
    for t in (1, 2, 3, 4, 6):
        packet = demand_three_power_joint_quotient(
            4, t, ((2, 12), (3, 8), (5, 6), (10, 4)), moving_width=8
        )
        x = 3 ** (1 << t)
        u = (x - 1) >> (t + 2)
        assert packet.crt_source == x % packet.crt_modulus
        assert packet.crt_unit == u % packet.crt_modulus
        for p, current, following in zip(
            packet.radix_ports,
            packet.unit_by_radix,
            packet.following_unit_by_radix,
            strict=True,
        ):
            assert current == u % p.modulus
            assert following == ((3 ** (1 << (t + 1)) - 1) >> (t + 3)) % p.modulus
        assert packet.source_power_evaluations == 4
        assert packet.small_modulus_squarings == 8
        assert packet.candidate_modulus_squarings == 0
        assert packet.terminal_status == "UNKNOWN"


def test_joint_terminal_f4_f5_and_radial_separation() -> None:
    f4 = FermatNumberSpec(4).demand_joint_three_power_quotient(15)
    f5 = FermatNumberSpec(5).demand_joint_three_power_quotient(31)
    d4 = {p.base: p for p in f4.radix_ports}
    d5 = {p.base: p for p in f5.radix_ports}
    assert d4[10].source_residue % 1000 == 761
    assert d5[10].source_residue % 1000 == 361
    assert d4[10].boundaries[2].tripling_carry == 2
    assert d5[10].boundaries[2].tripling_carry == 1
    assert f4.pivot.action_id == f5.pivot.action_id
    assert f4.walsh64.full_walsh != f5.walsh64.full_walsh
    assert f4.radial.advance(16) == f5.radial
    assert f4.crt_coverage == f5.crt_coverage == "insufficient-finite-CRT-precision"
    assert all(p.work[0].scalar_power_compositions == 1 for p in f4.radix_ports)
    assert f4.source_power_evaluations == len(DEFAULT_RADIX_DEMANDS)


def test_walsh_packet_is_lazy_until_observed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import (
        three_power_joint_quotient as joint,
    )

    def forbidden(_cls: type[SourceWalsh64], _level: int) -> SourceWalsh64:
        raise AssertionError("Walsh transform was evaluated during source demand")

    monkeypatch.setattr(joint.SourceWalsh64, "at", classmethod(forbidden))
    packet = demand_three_power_joint_quotient(4, 15, ((2, 8), (5, 4)), moving_width=0)
    assert packet.crt_modulus > 1
    with pytest.raises(AssertionError, match="Walsh transform"):
        _ = packet.walsh64


def test_walsh_source_resolves_one_level_then_squares(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import (
        three_power_joint_quotient as joint,
    )

    calls: list[int] = []
    original = joint._binary_source_low

    def spy(level: int, width: int = 64) -> int:
        calls.append(level)
        return original(level, width)

    monkeypatch.setattr(joint, "_binary_source_low", spy)
    packet = SourceWalsh64.at(17)

    assert calls == [16]
    assert packet.source_bits == original(17)


def test_h5_matches_naive_shift_and_repeat() -> None:
    for width in range(1, 20):
        for value in (0, 1, 2, 3, 5, (1 << width) - 1):
            value &= (1 << width) - 1
            expected = WalshH5.from_mask(value, width)
            for split in range(width + 1):
                lower = WalshH5.from_mask(value & ((1 << split) - 1), split)
                upper = WalshH5.from_mask(value >> split, width - split)
                assert lower.then(upper) == expected
            for copies in range(7):
                mask = sum(value << (width * k) for k in range(copies))
                assert expected.repeat(copies) == WalshH5.from_mask(
                    mask, copies * width
                )


def test_full_walsh_is_invertible_on_exact_64bit_masks() -> None:
    for mask in (0, 1, 2, 3, 0xFEDCBA9876543210, (1 << 64) - 1):
        spectrum = walsh64(mask)
        assert spectrum[0] == mask.bit_count()
        # The Hadamard transform is its own inverse up to scale 64.
        for bit in range(64):
            recovered = (
                sum(
                    spectrum[j] * (1 if (j & bit).bit_count() % 2 == 0 else -1)
                    for j in range(64)
                )
                // 64
            )
            # Here j is the spectral position and bit is the spatial position.
            assert recovered == (mask >> bit) & 1


def test_long_level_fixed_precision_is_bounded_and_stationary() -> None:
    p = FermatNumberSpec(1_000_000).demand_joint_three_power_quotient(
        10**9, ((2, 16), (3, 10), (10, 4)), moving_width=0
    )
    q = p.advance(10**12, moving_width=0)
    assert p.crt_unit != 0
    assert p.crt_modulus == q.crt_modulus
    assert p.pivot.action_id == q.pivot.action_id
    assert q.moving_unit_xor is None
    assert p.candidate_modulus_squarings == q.candidate_modulus_squarings == 0


def test_guards_and_generalized_crt() -> None:
    assert _join_crt((1, 4), (5, 6)) == (5, 12)
    with pytest.raises(ValueError, match="inconsistent"):
        _join_crt((0, 4), (1, 2))
    spec = FermatNumberSpec(4)
    with pytest.raises(ValueError, match="duplicate"):
        spec.demand_joint_three_power_quotient(15, ((10, 3), (10, 3)))
    with pytest.raises(ValueError, match="budget"):
        spec.demand_joint_three_power_quotient(15, ((10, 20),))
    with pytest.raises(ValueError, match="level-exceeds"):
        spec.demand_joint_three_power_quotient(16, ((10, 3),))


def test_walsh_source_masks_match_independent_literal_integer() -> None:
    from number_compiler.sequences.power_numbers.three_power_joint_quotient import (
        SourceWalsh64,
    )

    for t in range(1, 9):
        before, now, after = (3 ** (1 << j) for j in (t - 1, t, t + 1))
        packet = SourceWalsh64.at(t)
        assert packet.source_bits == now & ((1 << 64) - 1)
        trip_low = trip_high = borrow_mask = difference_mask = 0
        for j in range(1, 65):
            m = 1 << j
            a, b, c = before % m, now % m, after % m
            trit = (3 * b) // m
            trip_low |= (trit & 1) << (j - 1)
            trip_high |= (trit >> 1) << (j - 1)
            borrow_mask |= int(c < b) << (j - 1)
            difference_mask |= int((c - b) % m < (b - a) % m) << (j - 1)
        assert packet.tripling_carry_low == trip_low
        assert packet.tripling_carry_high == trip_high
        assert packet.innovation_borrow == borrow_mask
        assert packet.successive_borrow == difference_mask
        assert packet.innovation_xor == (trip_low ^ difference_mask)
        for mask, h5, spectrum in zip(
            (
                packet.source_bits,
                trip_low,
                trip_high,
                borrow_mask,
                difference_mask,
                packet.innovation_xor,
            ),
            packet.h5,
            packet.full_walsh,
            strict=True,
        ):
            assert h5 == WalshH5.from_mask(mask, 64)
            assert spectrum == walsh64(mask)
            assert tuple(value % 5 for value in spectrum) == walsh64_mod5(mask)


def test_joint_source_authenticity_and_terminal_fail_closed() -> None:
    from dataclasses import replace

    from number_compiler.sequences.power_numbers.certificate import (
        fermat_depth_certificate,
        mersenne_depth_certificate,
    )

    f4 = FermatNumberSpec(4).demand_joint_three_power_quotient(15)
    with pytest.raises(ValueError, match="normalized-unit CRT"):
        replace(f4, crt_unit=(f4.crt_unit + 1) % f4.crt_modulus)
    forged_units = list(f4.unit_by_radix)
    forged_units[0] = (forged_units[0] + 1) % f4.radix_ports[0].modulus
    with pytest.raises(ValueError, match="normalized unit does not match"):
        replace(f4, unit_by_radix=tuple(forged_units))
    with pytest.raises(ValueError, match="source/radial clock"):
        replace(f4, level=14)
    with pytest.raises(TypeError):
        changes: dict[str, object] = {"walsh64": replace(f4.walsh64, source_bits=0)}
        unchecked_replace = cast(Callable[..., object], replace)
        unchecked_replace(f4, **changes)
    for n in (4, 5):
        certificate = fermat_depth_certificate(n)
        assert certificate.status == "unknown"
        assert certificate.specialization_raw_squarings == 0
    for p in (11, 13):
        certificate = mersenne_depth_certificate(p)
        assert certificate.status == "unknown"
        assert certificate.specialization_raw_squarings == 0
    with pytest.raises(ValueError, match="moving-pivot-precision-budget"):
        FermatNumberSpec(1_000_000).demand_joint_three_power_quotient(
            10**9, ((10, 3),), moving_width=12
        )
