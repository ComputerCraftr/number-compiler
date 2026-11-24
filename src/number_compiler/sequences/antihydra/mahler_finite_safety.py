"""Bounded rational safety from one authenticated Mahler source."""

from __future__ import annotations

from collections.abc import Callable
from fractions import Fraction
from typing import TYPE_CHECKING, TypedDict

from number_compiler.arithmetic.fields.consumer_pullback import ExactRational
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.sequences.antihydra.mahler_harmonic_ring import (
    MahlerFixedOddHarmonicRing,
)
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointFutureAction,
)
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MAX_MAHLER_SOURCE_EXTENT,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.runtime import ArithmeticResult


class FiniteSafetyPacket(TypedDict):
    disposition: str
    requested_ticks: int
    completed_ticks: int
    first_unsafe_tick: int | None
    integer_endpoint: int
    fractional_endpoint: str
    clock_unit: str


def _admitted(source: int, fraction: Fraction, action: MahlerJointFutureAction) -> bool:
    return action.admits(
        source, ExactRational(fraction.numerator, fraction.denominator)
    )


def _advance(
    source: int, fraction: Fraction, action: MahlerJointFutureAction
) -> tuple[int, Fraction]:
    endpoint, tail = action.apply(
        source, ExactRational(fraction.numerator, fraction.denominator)
    )
    return endpoint, Fraction(tail.numerator, tail.denominator)


def _first_zero_failure(fraction: Fraction, span: int) -> int:
    """Locate the first failed half-open cut of a source-admitted zero run."""
    lo, hi = 0, span
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if 2 * fraction.numerator * 3**mid < fraction.denominator * (1 << mid):
            lo = mid
        else:
            hi = mid
    return hi


def _first_odd_failure(fraction: Fraction, span: int) -> int:
    if fraction < Fraction(1, 3):
        return 1
    if span == 1:
        raise ArithmeticError("a safe odd step has no failing cut")
    return 1 + _first_zero_failure((3 * fraction - 1) / 2, span - 1)


def certify_finite_safety(
    source: int,
    tail: Fraction,
    horizon: int,
    *,
    reserve_bits: Callable[[int], None],
) -> FiniteSafetyPacket:
    """Evaluate an exact finite rational inlet and retain only its safe endpoint.

    The run factory admits each supplied source. A failed action is descended
    by its guarded repeat and the exact even-run threshold.
    """
    if type(source) is not int or source <= 0 or type(tail) is not Fraction:
        raise TypeError("finite safety requires a positive source and exact fraction")
    if type(horizon) is not int or not 0 <= horizon <= MAX_MAHLER_SOURCE_EXTENT:
        raise ValueError("finite safety horizon must be between 0 and 4096 ticks")
    if not callable(reserve_bits):
        raise TypeError("finite safety requires a scratch reservation owner")
    current, fraction, completed = source, tail, 0
    failure: int | None = None
    if not 0 <= fraction < Fraction(1, 2):
        failure = 0
    while failure is None and completed < horizon:
        remaining = horizon - completed
        reserve_bits(
            32
            * (
                current.bit_length()
                + abs(fraction.numerator).bit_length()
                + fraction.denominator.bit_length()
                + 8 * remaining
                + 128
            )
        )
        ring: MahlerFixedOddHarmonicRing | None = None
        copies = 0
        if current & 1:
            if fraction < Fraction(1, 3):
                failure = completed + 1
                break
            exponent = v2_positive(3 * current + 1)
            if exponent <= remaining:
                ring = MahlerFixedOddHarmonicRing.from_source(current)
                copies = min(ring.capacity, remaining // exponent)
                if copies < 1:
                    raise ArithmeticError("odd source has no admitted return")
                action = ring.action(copies).joint
            else:
                action = MahlerJointFutureAction.bit(1).then(
                    MahlerJointFutureAction.zero_run(remaining - 1)
                )
        else:
            action = MahlerJointFutureAction.zero_run(
                min(v2_positive(current), remaining)
            )
        if not action.integer_admits(current):
            raise ArithmeticError("finite action has another source cylinder")
        if _admitted(current, fraction, action):
            current, fraction = _advance(current, fraction, action)
            completed += action.extent
            continue
        if ring is None:
            failure_in_action = (
                _first_odd_failure(fraction, action.extent)
                if current & 1
                else _first_zero_failure(fraction, action.extent)
            )
        else:
            lo, hi = 0, copies
            while lo + 1 < hi:
                mid = (lo + hi) // 2
                if _admitted(current, fraction, ring.action(mid).joint):
                    lo = mid
                else:
                    hi = mid
            if lo:
                prior = ring.action(lo).joint
                current, fraction = _advance(current, fraction, prior)
                completed += prior.extent
            failure_in_action = _first_odd_failure(fraction, ring.exponent)
        safe_steps = failure_in_action - 1
        if safe_steps:
            prefix = (
                MahlerJointFutureAction.bit(1).then(
                    MahlerJointFutureAction.zero_run(safe_steps - 1)
                )
                if current & 1
                else MahlerJointFutureAction.zero_run(safe_steps)
            )
            current, fraction = _advance(current, fraction, prefix)
            completed += safe_steps
        failure = completed + 1
    return {
        "disposition": "safe-prefix" if failure is None else "unsafe",
        "requested_ticks": horizon,
        "completed_ticks": completed,
        "first_unsafe_tick": failure,
        "integer_endpoint": current,
        "fractional_endpoint": str(fraction),
        "clock_unit": "physical-recurrence-ticks",
    }


def finite_safety(
    result: ArithmeticResult, tail: Fraction, horizon: int
) -> FiniteSafetyPacket:
    """Bind the finite safety calculation to a live Antihydra occurrence."""
    from number_compiler.sequences.antihydra.runtime import ArithmeticResult

    if type(result) is not ArithmeticResult:
        raise TypeError("finite safety requires an issued Antihydra result")
    result.require_source()
    scratch = RunArithmeticWorkspace.for_ledger(result.ledger, "mahler_finite_safety")
    with scratch.scope():
        return certify_finite_safety(
            result.h - 1, tail, horizon, reserve_bits=scratch.require_bits
        )
