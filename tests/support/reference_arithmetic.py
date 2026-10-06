"""Independent literal test references; never use the compiled operation under test."""

from __future__ import annotations

import random
from collections.abc import Sequence
from fractions import Fraction

from devtools.verification.oracles.sequence_arithmetic import (
    collatz_literal,
)
from devtools.verification.oracles.sequence_arithmetic import (
    reverse_add_literal as literal_reverse_add,
)
from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
)
from number_compiler.arithmetic.fields.consumer_pullback import SaturatingAffineAction
from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw

__all__ = ("collatz_literal", "literal_reverse_add", "literal_reverse_add_digits")


def literal_reverse_add_digits(
    seed: int, steps: int, base: int = 10
) -> tuple[int, ...]:
    """Return LSD-first digits from the independent reverse/add oracle.

    Decimal cases share the canonical literal oracle.  Other radices use a
    small direct arithmetic loop so scheduler tests can compare the existing
    nondecimal path without duplicating digit conversion in each test module.
    """
    if type(seed) is not int or seed < 0:
        raise ValueError("reverse/add seed must be a nonnegative integer")
    if type(steps) is not int or steps < 0:
        raise ValueError("reverse/add steps must be a nonnegative integer")
    if type(base) is not int or base < 2:
        raise ValueError("reverse/add base must be at least two")

    value = literal_reverse_add(seed, steps) if base == 10 else seed
    if base != 10:
        for _ in range(steps):
            digits = _radix_digits(value, base)
            reverse = sum(
                digit * base**index for index, digit in enumerate(reversed(digits))
            )
            value += reverse
    return _radix_digits(value, base)


def _radix_digits(value: int, base: int) -> tuple[int, ...]:
    digits: list[int] = []
    while True:
        value, digit = divmod(value, base)
        digits.append(digit)
        if value == 0:
            return tuple(digits)


def rational_action_components(
    action: SaturatingAffineAction,
) -> tuple[Fraction, Fraction, Fraction | None]:
    """Read production coefficients as independent standard-library rationals."""
    return (
        Fraction(action.scale.numerator, action.scale.denominator),
        Fraction(action.offset.numerator, action.offset.denominator),
        None
        if action.cap is None
        else Fraction(action.cap.numerator, action.cap.denominator),
    )


def literal_mahler_step(
    source: int, scale: Fraction, offset: Fraction, cap: Fraction | None
) -> tuple[int, Fraction, Fraction, Fraction | None]:
    """Fold one centered scalar branch with independent rational arithmetic.

    The centered source is one less than the arithmetic image source, so its
    odd bit is the complement of that image's parity bit.
    """
    bit = source & 1
    local_offset = Fraction(-3 * bit, 2)
    local_cap = Fraction(3 if bit else 9, 4)
    offset = Fraction(3, 2) * offset + local_offset
    cap = (
        local_cap
        if cap is None
        else min(Fraction(3, 2) * cap + local_offset, local_cap)
    )
    return (3 * source + bit) // 2, scale * Fraction(3, 2), offset, cap


def negacyclic_reduce(values: Sequence[int], classes: int) -> tuple[int, ...]:
    out = [0] * classes
    for index, value in enumerate(values):
        quotient, target = divmod(index, classes)
        out[target] = (out[target] + (-value if quotient & 1 else value)) % 32
    return tuple(out)


def physical_collatz_literal(seed: int, steps: int) -> int:
    value = seed
    for _ in range(steps):
        value = value // 2 if value % 2 == 0 else 3 * value + 1
    return value


def symmetric_word(rng: random.Random, base: int, width: int) -> tuple[int, ...]:
    half = [rng.randrange(2 * base - 1) for _ in range((width + 1) // 2)]
    if half[0] == 0:
        half[0] = 1
    return tuple(half + (half[-2::-1] if width & 1 else half[::-1]))


def carry_summary(symbols: tuple[int, ...]) -> ReverseCarrySectorTransfer:
    value = ReverseCarrySectorTransfer.leaf(10, symbols[0])
    for symbol in symbols[1:]:
        value = value.then(ReverseCarrySectorTransfer.leaf(10, symbol))
    return value


def reverse_add_digit_step(
    digits: tuple[int, ...], base: int
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Literal LSD-first addition with independently recorded carry boundaries."""
    output = []
    carries = [0]
    for left, right in zip(digits, reversed(digits), strict=True):
        carry, digit = divmod(left + right + carries[-1], base)
        carries.append(carry)
        output.append(digit)
    if carries[-1]:
        output.append(carries[-1])
    return tuple(output), tuple(carries)


def literal_events(value: int, events: int) -> tuple[int, int]:
    """Literal Syracuse events and accumulated shifts, independent of power DAGs."""
    shift = 0
    for _ in range(events):
        raw = 3 * value + 1
        valuation = (raw & -raw).bit_length() - 1
        value = raw >> valuation
        shift += valuation
    return value, shift


def literal_dyadic_orbit(
    source: int, width: int, law: DyadicReturnLaw
) -> tuple[int, int, int, int, int]:
    """Apply the declared integer branches directly, independently of compiled effects."""
    value, word, odd, delta, minimum = source, 0, 0, 0, 0
    for index in range(width):
        bit = value % 2
        word |= bit << index
        odd += bit
        delta += law.weights[bit]
        minimum = min(minimum, delta)
        value = (law.gains[bit] * value + law.offsets[bit]) // 2
    return value, word, odd, delta, minimum
