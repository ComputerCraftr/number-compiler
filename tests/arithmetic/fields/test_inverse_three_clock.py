"""Shared inverse-unit clock arithmetic; no sequence source admission."""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

import pytest

from number_compiler.arithmetic.fields.inverse_three_clock import InverseThreeClock


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
