"""Source-bound finite safety agrees with independent rational iteration."""

from __future__ import annotations

from fractions import Fraction
from random import Random

import pytest

from number_compiler.sequences.antihydra.mahler_finite_safety import (
    certify_finite_safety,
    finite_safety,
)
from number_compiler.sequences.antihydra.mahler_harmonic_ring import (
    MahlerFixedOddHarmonicRing,
)
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointFutureAction,
)
from number_compiler.sequences.antihydra.runtime import (
    AntihydraArithmeticTerm,
    ArithmeticResult,
)


def _literal(
    source: int, tail: Fraction, horizon: int
) -> tuple[int | None, int, Fraction]:
    if not 0 <= tail < Fraction(1, 2):
        return 0, source, tail
    for tick in range(1, horizon + 1):
        parity = source & 1
        following = (3 * tail - parity) / 2
        if not 0 <= following < Fraction(1, 2):
            return tick, source, tail
        source = (3 * source + parity) // 2
        tail = following
    return None, source, tail


def test_source_seven_and_initial_guard() -> None:
    term = AntihydraArithmeticTerm(0, shared_cache=False)
    result = term.result()
    assert finite_safety(result, Fraction(1, 3), 4)["first_unsafe_tick"] == 2
    assert finite_safety(result, Fraction(1, 2), 0)["first_unsafe_tick"] == 0
    assert finite_safety(result, Fraction(1, 3), 0)["completed_ticks"] == 0


def test_exact_rational_sources_against_literal() -> None:
    rng = Random(74601)
    for _ in range(1200):
        source = rng.randrange(1, 1 << 24)
        denominator = rng.randrange(1, 200)
        tail = Fraction(rng.randrange(denominator), denominator)
        horizon = rng.randrange(0, 130)
        expected_failure, expected_source, expected_tail = _literal(
            source, tail, horizon
        )
        packet = certify_finite_safety(
            source, tail, horizon, reserve_bits=lambda _: None
        )
        assert packet["first_unsafe_tick"] == expected_failure
        assert packet["integer_endpoint"] == expected_source
        assert packet["fractional_endpoint"] == str(expected_tail)
        assert packet["completed_ticks"] == (
            horizon if expected_failure is None else max(0, expected_failure - 1)
        )


def test_certified_run_uses_no_source_prefix_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("replayed a source prefix")

    monkeypatch.setattr(MahlerJointFutureAction, "from_source_prefix", forbidden)
    packet = certify_finite_safety(
        1 << 300, Fraction(0), 256, reserve_bits=lambda _: None
    )
    assert packet["disposition"] == "safe-prefix"
    assert packet["integer_endpoint"] == 3**256 * (1 << 44)


def test_authenticated_repeated_odd_run_powers_before_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source, modulus = MahlerFixedOddHarmonicRing.source_cylinder(3, 80)
    source = source or modulus
    count = 0
    original = MahlerJointFutureAction.then

    def counted(
        first: MahlerJointFutureAction, following: MahlerJointFutureAction
    ) -> MahlerJointFutureAction:
        nonlocal count
        count += 1
        return original(first, following)

    monkeypatch.setattr(MahlerJointFutureAction, "then", counted)
    expected_failure, endpoint, tail = _literal(source, Fraction(9, 19), 240)
    packet = certify_finite_safety(
        source, Fraction(9, 19), 240, reserve_bits=lambda _: None
    )
    assert expected_failure is None
    assert packet["disposition"] == "safe-prefix"
    assert packet["integer_endpoint"] == endpoint
    assert packet["fractional_endpoint"] == str(tail)
    assert count < 40


def test_reservation_and_source_validation() -> None:
    term = AntihydraArithmeticTerm(0, shared_cache=False)
    result = term.result()

    def refuse(_bits: int) -> None:
        raise MemoryError("scratch refused")

    with pytest.raises(MemoryError, match="scratch refused"):
        certify_finite_safety(7, Fraction(1, 3), 1, reserve_bits=refuse)
    with pytest.raises(ValueError, match="unbound"):
        finite_safety(object.__new__(ArithmeticResult), Fraction(1, 3), 1)
    with pytest.raises(ValueError, match="horizon"):
        finite_safety(result, Fraction(0), 4097)
