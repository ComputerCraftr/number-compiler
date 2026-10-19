"""Bounded joint observer audit for the comma temporal clock.

This module is an audit oracle.  It does not define a native decade action or
promote a temporal quotient to production.  One abstract clock tick performs
one ``comma_port_next`` transition for each of the 90 zero-inclusive source
ports and advances the harmonic exponent by one.  The relationship between
that clock and a native decade remains a separate theorem obligation.

The complete observer retained here is deliberately explicit but bounded:

* the 90 endpoint digits;
* the nine exact ``10^r mod c`` core responses;
* the recursive ``PairLanguage`` Q21 word state;
* the recursive radix-9 word state (length modulo 6 and value modulo 9);
* the six-element last-reset germ; and
* the exact first non-neutral pair sum.

The byte signature is a concatenation of those fixed-width fields.  It is
used as an exact key, never as a hash or a retained literal history.  The
state has a transient of three ticks and then period 13,860 for this declared
abstract observer.  That numerical result is finite-audit evidence only.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.sequences.comma.arithmetic import (
    comma_port_next,
    comma_port_previous,
)

from .comma_pair_language import PAIR_IDENTITY, PairLanguage

HARMONIC_CORES: tuple[int, ...] = (1, 3, 7, 11, 13, 21, 23, 27, 29)
PORTS: tuple[tuple[int, int], ...] = tuple(
    (leading, digit) for leading in range(1, 10) for digit in range(10)
)
PORT_COUNT = len(PORTS)
ABSTRACT_PERIOD = 13_860
ABSTRACT_TRANSIENT = 3
MAX_TRACE_LENGTH = ABSTRACT_PERIOD + ABSTRACT_TRANSIENT + 1
DYADIC_PERIOD = 60
DYADIC_TRANSIENT = 2


def _port_index(leading: int, source_digit: int) -> int:
    if (
        type(leading) is not int
        or not 1 <= leading <= 9
        or type(source_digit) is not int
        or not 0 <= source_digit <= 9
    ):
        raise ValueError("unknown comma source port")
    return (leading - 1) * 10 + source_digit


def _validate_pair_sum(pair_sum: int) -> None:
    if type(pair_sum) is not int or not 0 <= pair_sum <= 18:
        raise ValueError("comma pair sum must be in 0..18")


@dataclass(frozen=True, slots=True)
class Radix9Word:
    """Exact recursive F9 action with length phase modulo six."""

    length_mod6: int
    value_mod9: int

    def __post_init__(self) -> None:
        if type(self.length_mod6) is not int or not 0 <= self.length_mod6 < 6:
            raise ValueError("radix-9 word length must be in 0..5")
        if type(self.value_mod9) is not int or not 0 <= self.value_mod9 < 9:
            raise ValueError("radix-9 word value must be in 0..8")

    @classmethod
    def identity(cls) -> Radix9Word:
        return cls(0, 0)

    @classmethod
    def atom(cls, pair_sum: int) -> Radix9Word:
        _validate_pair_sum(pair_sum)
        return cls(1, pair_sum % 9)

    def then(self, right: Radix9Word) -> Radix9Word:
        if type(right) is not Radix9Word:
            raise TypeError("radix-9 words compose with radix-9 words")
        return Radix9Word(
            (self.length_mod6 + right.length_mod6) % 6,
            (self.value_mod9 + pow(2, self.length_mod6, 9) * right.value_mod9) % 9,
        )


def dyadic_duration_representative(level: int) -> int:
    """Return the finite-period representative for abstract duration ``2^level``.

    Levels 0 and 1 are the two dyadic transients.  For level at least two the
    candidate abstract period allows reduction modulo 13,860; the separate
    60-period claim is checked by the audit tests rather than assumed here.
    """

    if type(level) is not int or level < 0:
        raise ValueError("dyadic level must be a nonnegative integer")
    if level < DYADIC_TRANSIENT:
        return 1 << level
    duration_mod_period = pow(2, level, ABSTRACT_PERIOD)
    return ABSTRACT_TRANSIENT + (
        (duration_mod_period - ABSTRACT_TRANSIENT) % ABSTRACT_PERIOD
    )


def _carry_code(carry: CarryFn) -> int:
    if carry is CarryFn.CONST0:
        return 0
    if carry is CarryFn.ID:
        return 1
    if carry is CarryFn.CONST1:
        return 2
    raise AssertionError("unreachable carry member")


def _pair_language_bytes(language: PairLanguage) -> bytes:
    """Encode one Q21 word state without retaining its source word."""

    # ``first`` is the PairLanguage midpoint code, not the exact first sum;
    # the latter is retained separately by ``first_defect`` below.
    first = 0 if language.first is None else language.first + 1
    return bytes(
        (_carry_code(language.carry), language.f2, language.f5, first, language.phase)
    )


def _reset_code(pair_sum: int) -> int:
    """Encode the Comma_Reset_Germ carrier (0 = I, 1..5 = R(0..4))."""

    _validate_pair_sum(pair_sum)
    if pair_sum == 9:
        return 0
    # This is the executable form of comma_reset_germ_encode: lower sums use
    # s-9, upper sums use 9-s.  Adding one reserves byte 0 for identity.
    eta = (pair_sum - 9) % 5 if pair_sum < 9 else (9 - pair_sum) % 5
    return eta + 1


def _first_sum_code(pair_sum: int) -> int:
    """Encode the first non-neutral sum (0 = no such event yet)."""

    _validate_pair_sum(pair_sum)
    if pair_sum == 9:
        return 0
    # The +1 makes physical sum 0 distinguishable from the absent sentinel.
    return pair_sum + 1


@dataclass(frozen=True, slots=True)
class JointObserverState:
    """One complete exact-byte state of the bounded abstract observer."""

    port_vector: bytes
    harmonic_phase: bytes
    q21: bytes
    radix9: bytes
    reset_germ: bytes
    first_defect: bytes

    def __post_init__(self) -> None:
        if len(self.port_vector) != PORT_COUNT:
            raise ValueError("comma observer requires 90 endpoint digits")
        if len(self.harmonic_phase) != len(HARMONIC_CORES):
            raise ValueError("comma observer requires nine harmonic cores")
        if len(self.q21) != 5 * PORT_COUNT:
            raise ValueError("comma observer Q21 width mismatch")
        if len(self.radix9) != 2 * PORT_COUNT:
            raise ValueError("comma observer radix-9 width mismatch")
        if len(self.reset_germ) != PORT_COUNT:
            raise ValueError("comma observer reset width mismatch")
        if len(self.first_defect) != PORT_COUNT:
            raise ValueError("comma observer first-defect width mismatch")

    @property
    def signature(self) -> bytes:
        """An exact fixed-width key; no digest or literal history is used."""

        return (
            self.port_vector
            + self.harmonic_phase
            + self.q21
            + self.radix9
            + self.reset_germ
            + self.first_defect
        )


class _JointObserverMachine:
    """Mutable builder used only while emitting bounded audit states."""

    __slots__ = ("digits", "first", "harmonic", "languages", "radix9", "reset")

    def __init__(self) -> None:
        self.digits = [digit for _, digit in PORTS]
        self.languages = [PAIR_IDENTITY for _ in PORTS]
        self.radix9 = [Radix9Word.identity() for _ in PORTS]
        self.reset = [0 for _ in PORTS]
        self.first = [0 for _ in PORTS]
        self.harmonic = [pow(10, 0, core) % core for core in HARMONIC_CORES]

    def state(self) -> JointObserverState:
        return JointObserverState(
            bytes(self.digits),
            bytes(self.harmonic),
            b"".join(_pair_language_bytes(language) for language in self.languages),
            bytes(
                value
                for word in self.radix9
                for value in (word.length_mod6, word.value_mod9)
            ),
            bytes(self.reset),
            bytes(self.first),
        )

    def advance(self) -> None:
        """Perform exactly one abstract port and harmonic-clock tick."""

        for index, (leading, _source_digit) in enumerate(PORTS):
            digit = self.digits[index]
            previous = comma_port_previous(leading, digit)
            pair_sum = digit + previous
            self.languages[index] = self.languages[index].then(
                PairLanguage.leaf(pair_sum)
            )
            self.radix9[index] = self.radix9[index].then(Radix9Word.atom(pair_sum))
            if pair_sum != 9:
                if self.first[index] == 0:
                    self.first[index] = _first_sum_code(pair_sum)
                # The last non-neutral event replaces the reset germ; neutral
                # sum 9 preserves it.  This is comma_reset_compose in byte form.
                self.reset[index] = _reset_code(pair_sum)
            self.digits[index] = comma_port_next(leading, digit)
        self.harmonic = [
            (value * 10) % core
            for value, core in zip(self.harmonic, HARMONIC_CORES, strict=True)
        ]


def joint_observer_trace(
    limit: int = ABSTRACT_PERIOD + ABSTRACT_TRANSIENT,
) -> tuple[JointObserverState, ...]:
    """Emit states for abstract ticks ``0 .. limit-1``.

    The default emits one complete period plus the three transient states.
    Each state is fixed-width and no source word or Moore history is retained.
    """

    if type(limit) is not int or not 0 <= limit <= MAX_TRACE_LENGTH:
        raise ValueError(f"observer trace limit must be in 0..{MAX_TRACE_LENGTH}")
    machine = _JointObserverMachine()
    states: list[JointObserverState] = []
    for _ in range(limit):
        states.append(machine.state())
        machine.advance()
    return tuple(states)


def q21_port_bytes(state: JointObserverState, leading: int, source_digit: int) -> bytes:
    """Extract one five-byte Q21 state from a complete observer state."""

    index = _port_index(leading, source_digit)
    start = 5 * index
    return state.q21[start : start + 5]


def reset_germ_code(state: JointObserverState, leading: int, source_digit: int) -> int:
    """Extract one reset-germ code (0 = I, 1..5 = R(0..4))."""

    index = _port_index(leading, source_digit)
    return state.reset_germ[index]


def radix9_port_bytes(
    state: JointObserverState, leading: int, source_digit: int
) -> bytes:
    """Extract one two-byte ``(length mod 6, value mod 9)`` state."""

    index = _port_index(leading, source_digit)
    start = 2 * index
    return state.radix9[start : start + 2]


__all__ = [
    "ABSTRACT_PERIOD",
    "ABSTRACT_TRANSIENT",
    "DYADIC_PERIOD",
    "DYADIC_TRANSIENT",
    "HARMONIC_CORES",
    "MAX_TRACE_LENGTH",
    "PORTS",
    "PORT_COUNT",
    "JointObserverState",
    "Radix9Word",
    "dyadic_duration_representative",
    "joint_observer_trace",
    "q21_port_bytes",
    "radix9_port_bytes",
    "reset_germ_code",
]
