"""Powered local carry-difference and decimal-borrow cocycle.

This module covers a synchronized fixed-sector pair with adjacent leading
digits ``f`` and ``f + 1``.  Its state is only the low-suffix difference and
the base suffix's ones digit.  The signed innovation is an exact local
cocycle; binding it to source-bound c1 returns reconstructs the paired high
prefix.  This local arithmetic does not select future comma branches or make
claims about a global future quotient.
"""

from __future__ import annotations

from dataclasses import dataclass

from .carry_generator import (
    BitsCharge,
    BoundC1Return,
    C1Phase,
    C1Return,
    WorkCharge,
    _charge,
)

_BORROW_PERIOD = 50
_BORROW_RETURN_SEAL = object()
_BOUND_BORROW_RETURN_SEAL = object()


def _borrow_signature(phase: BorrowPhase) -> tuple[int, int, int]:
    _validate_phase(phase)
    return phase.sector, phase.delta, phase.digit


def _validate_phase(phase: BorrowPhase) -> None:
    if type(phase) is not BorrowPhase:
        raise TypeError("borrow operation requires a BorrowPhase")
    if (
        type(phase.sector) is not int
        or not 1 <= phase.sector <= 8
        or type(phase.delta) is not int
        or not 0 <= phase.delta < 100
        or type(phase.digit) is not int
        or not 0 <= phase.digit < 10
    ):
        raise ValueError("invalid or forged comma borrow phase")


def _one_step(phase: BorrowPhase) -> tuple[BorrowPhase, int]:
    """Apply the exact adjacent-sector difference transition and innovation."""
    _validate_phase(phase)
    numerator = 11 * phase.delta + 1
    innovation = (
        numerator // 100 - phase.delta // 10 - int(phase.digit + phase.delta % 10 >= 10)
    )
    target = BorrowPhase(
        phase.sector,
        numerator % 100,
        (phase.digit + phase.sector) % 10,
    )
    return target, innovation


@dataclass(frozen=True, slots=True)
class BorrowPhase:
    """Local pair phase ``(f, (x_B-x_A) mod 100, x_A mod 10)``."""

    sector: int
    delta: int
    digit: int

    def __post_init__(self) -> None:
        _validate_phase(self)

    @classmethod
    def from_suffixes(
        cls, sector: int, base_suffix: int, sibling_suffix: int
    ) -> BorrowPhase:
        if (
            type(sector) is not int
            or not 1 <= sector <= 8
            or type(base_suffix) is not int
            or not 0 <= base_suffix < 100
            or type(sibling_suffix) is not int
            or not 0 <= sibling_suffix < 100
        ):
            raise ValueError("borrow suffixes require adjacent sector f=1..8")
        return cls(
            sector,
            (sibling_suffix - base_suffix) % 100,
            base_suffix % 10,
        )

    def step(self) -> tuple[BorrowPhase, int]:
        """Return the next phase and its signed normalized innovation."""
        return _one_step(self)

    def advance(
        self,
        steps: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> BorrowPhase:
        """Advance by a closed CRT action with period dividing 50."""
        if type(steps) is not int or steps < 0:
            raise ValueError("borrow duration must be a nonnegative exact integer")
        _validate_phase(self)
        _charge(
            charge_work,
            charge_bits,
            5,
            steps,
            self.sector,
            self.delta,
            self.digit,
            extra_bits=steps.bit_length() + 8,
        )
        residue = steps % _BORROW_PERIOD
        delta_phase = C1Phase(1, self.delta % 4, self.delta % 25).advance(
            residue,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        digit = (self.digit + self.sector * residue) % 10
        return BorrowPhase(self.sector, delta_phase.suffix, digit)


def _powered_return_summary(
    start: BorrowPhase,
    steps: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> tuple[BorrowPhase, int]:
    """Return endpoint and innovation from the shared powered c1 owner.

    The local innovation depends only on ``delta`` and the base ones digit,
    not on either suffix's tens digit.  Choosing ``x_A=d`` therefore gives an
    exact representative pair, and the signed count difference plus endpoint
    borrow is the same cocycle.  The fixed 50-phase orbit is never replayed.
    """
    _validate_phase(start)
    if type(steps) is not int or steps < 0:
        raise ValueError("borrow duration must be a nonnegative exact integer")
    _charge(
        charge_work,
        charge_bits,
        8,
        steps,
        start.sector,
        start.delta,
        start.digit,
        extra_bits=2 * steps.bit_length() + 128,
    )
    base_suffix = start.digit
    sibling_suffix = (base_suffix + start.delta) % 100
    base = C1Return(
        C1Phase.from_suffix(start.sector, base_suffix),
        steps,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    sibling = C1Return(
        C1Phase.from_suffix(start.sector + 1, sibling_suffix),
        steps,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    source_borrow = int(sibling_suffix < base_suffix)
    target_borrow = int(sibling.target.suffix < base.target.suffix)
    target = BorrowPhase.from_suffixes(
        start.sector,
        base.target.suffix,
        sibling.target.suffix,
    )
    _charge(
        charge_work,
        charge_bits,
        3,
        base.count,
        sibling.count,
        source_borrow,
        target_borrow,
        steps,
        extra_bits=steps.bit_length() + 8,
    )
    innovation = sibling.count - base.count + source_borrow - target_borrow
    return target, innovation


def _return_signature(
    start: BorrowPhase,
    target: BorrowPhase,
    steps: int,
    innovation: int,
) -> tuple[int, ...]:
    if (
        type(steps) is not int
        or steps < 0
        or type(innovation) is not int
        or abs(innovation) > steps
    ):
        raise ValueError("invalid or forged comma borrow return counters")
    return (*_borrow_signature(start), *_borrow_signature(target), steps, innovation)


def _initialize_return(
    result: BorrowReturn,
    start: BorrowPhase,
    target: BorrowPhase,
    steps: int,
    innovation: int,
) -> None:
    """Initialize from an exact constructor or validated cocycle composition."""
    witness = _return_signature(start, target, steps, innovation)
    object.__setattr__(result, "_start", start)
    object.__setattr__(result, "_target", target)
    object.__setattr__(result, "_steps", steps)
    object.__setattr__(result, "_innovation", innovation)
    object.__setattr__(result, "_witness", witness)
    object.__setattr__(result, "_seal", _BORROW_RETURN_SEAL)


@dataclass(frozen=True, slots=True, init=False)
class BorrowReturn:
    """An exact powered return of the adjacent-sector local borrow phase."""

    _start: BorrowPhase
    _target: BorrowPhase
    _steps: int
    _innovation: int
    _witness: tuple[int, ...]
    _seal: object

    def __init__(
        self,
        start: BorrowPhase,
        steps: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> None:
        if type(start) is not BorrowPhase:
            raise TypeError("borrow return requires a BorrowPhase source")
        _validate_phase(start)
        if type(steps) is not int or steps < 0:
            raise ValueError("borrow duration must be a nonnegative exact integer")
        _charge(
            charge_work,
            charge_bits,
            8,
            steps,
            start.sector,
            start.delta,
            start.digit,
            extra_bits=2 * steps.bit_length() + 96,
        )
        target, innovation = _powered_return_summary(
            start,
            steps,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        _initialize_return(self, start, target, steps, innovation)

    def _validate(self) -> None:
        if getattr(self, "_seal", None) is not _BORROW_RETURN_SEAL:
            raise ValueError("invalid or uninitialized comma borrow return")
        signature = _return_signature(
            self._start,
            self._target,
            self._steps,
            self._innovation,
        )
        if getattr(self, "_witness", None) != signature:
            raise ValueError("comma borrow return fields disagree with snapshot")

    @property
    def start(self) -> BorrowPhase:
        self._validate()
        return self._start

    @property
    def target(self) -> BorrowPhase:
        self._validate()
        return self._target

    @property
    def steps(self) -> int:
        self._validate()
        return self._steps

    @property
    def innovation(self) -> int:
        self._validate()
        return self._innovation

    def then(
        self,
        after: BorrowReturn,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> BorrowReturn:
        """Compose adjacent returns without recomputing either innovation."""
        if type(after) is not BorrowReturn:
            raise ValueError("borrow returns have different chronological endpoints")
        self._validate()
        after._validate()
        if self._target != after._start:
            raise ValueError("borrow returns have different chronological endpoints")
        _charge(
            charge_work,
            charge_bits,
            2,
            self._steps,
            after._steps,
            self._innovation,
            after._innovation,
            extra_bits=2,
        )
        steps = self._steps + after._steps
        innovation = self._innovation + after._innovation
        return _completed_return(
            self._start,
            after._target,
            steps,
            innovation,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )


def _completed_return(
    start: BorrowPhase,
    target: BorrowPhase,
    steps: int,
    innovation: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> BorrowReturn:
    """Complete a return from exact child cocycles and check its endpoint."""
    if type(start) is not BorrowPhase or type(target) is not BorrowPhase:
        raise TypeError("completed borrow return requires exact phases")
    _charge(
        charge_work,
        charge_bits,
        1,
        steps,
        innovation,
        extra_bits=steps.bit_length() + 8,
    )
    if (
        start.advance(
            steps,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        != target
    ):
        raise ValueError("completed borrow target disagrees with its duration")
    result = object.__new__(BorrowReturn)
    _initialize_return(result, start, target, steps, innovation)
    return result


def _bound_signature(bound: BoundC1Return) -> tuple[int, ...]:
    bound._validate()
    action = bound._action
    return (
        bound._source_high,
        bound._target_high,
        *_phase_signature(action._start),
        *_phase_signature(action._target),
        action._steps,
        action._count,
    )


def _phase_signature(phase: C1Phase) -> tuple[int, int, int]:
    if type(phase) is not C1Phase:
        raise TypeError("paired return requires a C1Phase")
    # All public phase observations validate its finite coordinates.
    return phase.sector, phase.mod4, phase.mod25


def _paired_phase(base: C1Phase, sibling: C1Phase) -> BorrowPhase:
    if type(base) is not C1Phase or type(sibling) is not C1Phase:
        raise TypeError("paired borrow return requires C1 phases")
    base_suffix = base.suffix
    sibling_suffix = sibling.suffix
    if sibling.sector != base.sector + 1 or not 1 <= base.sector <= 8:
        raise ValueError("borrow pair requires adjacent sectors f and f+1")
    return BorrowPhase.from_suffixes(base.sector, base_suffix, sibling_suffix)


def _bound_witness(
    action: BorrowReturn,
    base: BoundC1Return,
    sibling: BoundC1Return,
    source_borrow: int,
    target_borrow: int,
) -> tuple[int, ...]:
    return (
        *_return_signature(
            action._start,
            action._target,
            action._steps,
            action._innovation,
        ),
        *_bound_signature(base),
        *_bound_signature(sibling),
        source_borrow,
        target_borrow,
    )


def _check_bound_pair(
    action: BorrowReturn,
    base: BoundC1Return,
    sibling: BoundC1Return,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> tuple[int, int]:
    """Check low endpoints, physical borrow, and normalized high cocycle."""
    action._validate()
    base._validate()
    sibling._validate()
    if base.steps != sibling.steps or action.steps != base.steps:
        raise ValueError("paired borrow returns must have equal durations")
    start = _paired_phase(base.start, sibling.start)
    target = _paired_phase(base.target, sibling.target)
    if action.start != start or action.target != target:
        raise ValueError("borrow action does not match paired c1 endpoints")
    source_borrow = int(sibling.start.suffix < base.start.suffix)
    target_borrow = int(sibling.target.suffix < base.target.suffix)
    _charge(
        charge_work,
        charge_bits,
        3,
        base.count,
        sibling.count,
        base.source_high,
        sibling.source_high,
        base.target_high,
        sibling.target_high,
        action.innovation,
        extra_bits=3,
    )
    count_difference = sibling.count - base.count
    if action.innovation != count_difference + source_borrow - target_borrow:
        raise ValueError("borrow innovation disagrees with paired c1 counts")
    source_difference = sibling.source_high - base.source_high - source_borrow
    target_difference = sibling.target_high - base.target_high - target_borrow
    if target_difference != source_difference + action.innovation:
        raise ValueError("normalized high-prefix difference disagrees with cocycle")
    return source_borrow, target_borrow


@dataclass(frozen=True, slots=True, init=False)
class BoundBorrowReturn:
    """A local borrow return bound to two adjacent source-bound c1 returns."""

    _action: BorrowReturn
    _base: BoundC1Return
    _sibling: BoundC1Return
    _source_borrow: int
    _target_borrow: int
    _witness: tuple[int, ...]
    _seal: object

    def __init__(self) -> None:
        raise TypeError("construct BoundBorrowReturn with bind_borrow_return")

    def _validate(self) -> None:
        if getattr(self, "_seal", None) is not _BOUND_BORROW_RETURN_SEAL:
            raise ValueError("invalid or uninitialized bound borrow return")
        self._action._validate()
        self._base._validate()
        self._sibling._validate()
        source_borrow = int(self._sibling.start.suffix < self._base.start.suffix)
        target_borrow = int(self._sibling.target.suffix < self._base.target.suffix)
        if (
            source_borrow != self._source_borrow
            or target_borrow != self._target_borrow
            or getattr(self, "_witness", None)
            != _bound_witness(
                self._action,
                self._base,
                self._sibling,
                source_borrow,
                target_borrow,
            )
        ):
            raise ValueError("bound borrow return fields disagree with snapshot")

    @property
    def action(self) -> BorrowReturn:
        self._validate()
        return self._action

    @property
    def steps(self) -> int:
        self._validate()
        return self._action.steps

    @property
    def innovation(self) -> int:
        self._validate()
        return self._action.innovation

    @property
    def base(self) -> BoundC1Return:
        self._validate()
        return self._base

    @property
    def sibling(self) -> BoundC1Return:
        self._validate()
        return self._sibling

    @property
    def source_borrow(self) -> int:
        self._validate()
        return self._source_borrow

    @property
    def target_borrow(self) -> int:
        self._validate()
        return self._target_borrow

    def normalized_high_difference(
        self,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> int:
        """Return the source ``H_B-H_A-b`` with a charged subtraction."""
        self._validate()
        _charge(
            charge_work,
            charge_bits,
            1,
            self._sibling.source_high,
            self._base.source_high,
            self._source_borrow,
            extra_bits=2,
        )
        return self._sibling.source_high - self._base.source_high - self._source_borrow

    def reconstruct_sibling_high(
        self,
        base_high_after: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> int:
        """Recover the sibling high prefix from the base and signed cocycle."""
        self._validate()
        if type(base_high_after) is not int or base_high_after < 0:
            raise ValueError("base high prefix must be a nonnegative exact integer")
        _charge(
            charge_work,
            charge_bits,
            2,
            base_high_after,
            self._base.source_high,
            self._sibling.source_high,
            self._action.innovation,
            self._source_borrow,
            self._target_borrow,
            extra_bits=3,
        )
        if base_high_after != self._base.target_high:
            raise ValueError("base high prefix does not match the bound return")
        reconstructed = (
            base_high_after
            + self._sibling.source_high
            - self._base.source_high
            + self._action.innovation
            - self._source_borrow
            + self._target_borrow
        )
        if reconstructed != self._sibling.target_high:
            raise ArithmeticError("borrow cocycle failed high-prefix reconstruction")
        return reconstructed

    def then(
        self,
        after: BoundBorrowReturn,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> BoundBorrowReturn:
        """Compose paired returns chronologically without replaying the orbit."""
        if type(after) is not BoundBorrowReturn:
            raise ValueError("bound borrow returns are not chronologically adjacent")
        self._validate()
        after._validate()
        base = self._base.then(
            after._base,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        sibling = self._sibling.then(
            after._sibling,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        action = self._action.then(
            after._action,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        return _completed_bound_return(
            action,
            base,
            sibling,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )


def _completed_bound_return(
    action: BorrowReturn,
    base: BoundC1Return,
    sibling: BoundC1Return,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> BoundBorrowReturn:
    """Bind child-derived returns and validate their shared cocycle endpoint."""
    if (
        type(action) is not BorrowReturn
        or type(base) is not BoundC1Return
        or type(sibling) is not BoundC1Return
    ):
        raise TypeError("completed bound borrow return requires exact returns")
    _charge(
        charge_work,
        charge_bits,
        4,
        action.steps,
        action.innovation,
        base.source_high,
        sibling.source_high,
        base.target_high,
        sibling.target_high,
        extra_bits=action.steps.bit_length() + 8,
    )
    source_borrow, target_borrow = _check_bound_pair(
        action,
        base,
        sibling,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    result = object.__new__(BoundBorrowReturn)
    object.__setattr__(result, "_action", action)
    object.__setattr__(result, "_base", base)
    object.__setattr__(result, "_sibling", sibling)
    object.__setattr__(result, "_source_borrow", source_borrow)
    object.__setattr__(result, "_target_borrow", target_borrow)
    object.__setattr__(
        result,
        "_witness",
        _bound_witness(action, base, sibling, source_borrow, target_borrow),
    )
    object.__setattr__(result, "_seal", _BOUND_BORROW_RETURN_SEAL)
    return result


def bind_borrow_return(
    base: BoundC1Return,
    sibling: BoundC1Return,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> BoundBorrowReturn:
    """Build and bind the exact adjacent-sector normalized borrow return."""
    if type(base) is not BoundC1Return or type(sibling) is not BoundC1Return:
        raise TypeError("borrow binding requires two BoundC1Return values")
    base._validate()
    sibling._validate()
    start = _paired_phase(base.start, sibling.start)
    if base.steps != sibling.steps:
        raise ValueError("paired borrow returns must have equal durations")
    action = BorrowReturn(
        start,
        base.steps,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    return _completed_bound_return(
        action,
        base,
        sibling,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


__all__ = [
    "BorrowPhase",
    "BorrowReturn",
    "BoundBorrowReturn",
    "bind_borrow_return",
]
