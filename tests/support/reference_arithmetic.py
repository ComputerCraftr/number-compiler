"""Independent literal test references; never use the compiled operation under test."""

from __future__ import annotations

from devtools.verification.oracles.sequence_arithmetic import (
    collatz_literal as collatz_literal,
)
from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw

import random
from collections.abc import Sequence

from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
)


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
