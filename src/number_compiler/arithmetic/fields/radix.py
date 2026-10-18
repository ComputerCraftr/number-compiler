"""Canonical small radix utilities shared by every sequence compiler.

These helpers are intentionally representation-only.  They never perform a
sequence transition and therefore cannot become a parallel semantic state.
"""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterable, Sequence
from typing import cast


def bit_width(value: int) -> int:
    """Return at least one bit for a nonnegative integer magnitude."""
    value = int(value)
    if value < 0:
        value = -value
    return max(1, value.bit_length())


def radix_width(
    number: int, base: int, *, charge_bits: Callable[[int], None] | None = None
) -> int:
    """Exact width, optionally charging power and comparison operand bits."""
    if type(number) is not int or number < 1 or type(base) is not int or base < 2:
        raise ValueError("radix width requires a positive integer and base >= 2")

    def power_below(exponent: int) -> bool:
        if charge_bits is not None:
            charge_bits(base.bit_length() + exponent.bit_length())
        candidate = cast(int, pow(base, exponent))
        if charge_bits is not None:
            charge_bits(candidate.bit_length() + number.bit_length())
        return candidate <= number

    upper = 1
    while power_below(upper):
        upper <<= 1
    lower = upper >> 1
    while lower + 1 < upper:
        middle = (lower + upper) >> 1
        if power_below(middle):
            lower = middle
        else:
            upper = middle
    return lower + 1


def digit_threshold_mask(base: int, threshold: int, bit: int) -> int:
    """Encode one side of a radix-digit threshold as a finite-domain mask.

    Bit zero denotes digits below ``threshold``; bit one denotes digits at
    or above it. This is the common representation for threshold carry ports.
    """
    if (
        type(base) is not int
        or base < 2
        or type(threshold) is not int
        or not 1 <= threshold < base
        or type(bit) is not int
        or bit not in (0, 1)
    ):
        raise ValueError((base, threshold, bit))
    lower = (1 << threshold) - 1
    return lower if bit == 0 else ((1 << base) - 1) ^ lower


def iter_digits_lsd(
    value: int,
    base: int,
    *,
    charge: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
    observe_workspace: Callable[[int, int], None] | None = None,
) -> Generator[int, None, None]:
    """Stream canonical digits using balanced radix splits and bounded leaves.

    Optional callbacks charge operations and operand-bit work before arithmetic.
    Workspace observations give live helper slots and integer payload bits;
    these are logical sizes, not Python heap-byte measurements. Closing the
    generator releases its worklists and reports zero live helper storage.
    """
    value, base = int(value), int(base)
    if value < 0 or base < 2:
        raise ValueError((value, base))

    def work(bits: int, operations: int = 1) -> None:
        if charge is not None:
            charge(operations)
        if charge_bits is not None:
            charge_bits(bits)

    powers: list[int] = []
    pending: list[tuple[int, int, bool]] = []
    try:
        work(value.bit_length() + base.bit_length())
        if value < base:
            if observe_workspace is not None:
                observe_workspace(1, value.bit_length())
            yield value
        elif base & (base - 1) == 0:
            digit_bits = base.bit_length() - 1
            remaining = (value.bit_length() + digit_bits - 1) // digit_bits
            work(value.bit_length())
            encoded = value.to_bytes((value.bit_length() + 7) // 8, "little")
            if observe_workspace is not None:
                observe_workspace(1, len(encoded) * 8 + 2 * digit_bits)
            accumulator = available = 0
            for byte in encoded:
                work(available + 8)
                accumulator |= byte << available
                available += 8
                while available >= digit_bits and remaining:
                    work(available + digit_bits)
                    digit = accumulator & (base - 1)
                    accumulator >>= digit_bits
                    available -= digit_bits
                    remaining -= 1
                    yield digit
            if remaining:
                work(available)
                yield accumulator
        else:
            # The only single-digit divisions operate on at most 32 digits.
            work(32 * base.bit_length())
            powers.append(base**32)
            power_bits = powers[0].bit_length()
            while powers[-1] <= value:
                work(2 * powers[-1].bit_length())
                powers.append(powers[-1] * powers[-1])
                power_bits += powers[-1].bit_length()
            pending.append((value, len(powers) - 1, False))
            pending_bits = value.bit_length()
            while pending:
                part, level, padded = pending.pop()
                pending_bits -= part.bit_length()
                if observe_workspace is not None:
                    observe_workspace(
                        len(powers) + len(pending) + 1,
                        power_bits + pending_bits + part.bit_length(),
                    )
                work(part.bit_length() + level.bit_length())
                if level:
                    divisor = powers[level - 1]
                    work(part.bit_length() + divisor.bit_length())
                    high, low = divmod(part, divisor)
                    if high or padded:
                        pending.append((high, level - 1, padded))
                        pending.append((low, level - 1, True))
                        pending_bits += high.bit_length() + low.bit_length()
                    else:
                        pending.append((low, level - 1, False))
                        pending_bits += low.bit_length()
                else:
                    emitted = 0
                    while part:
                        work(part.bit_length() + base.bit_length())
                        part, digit = divmod(part, base)
                        emitted += 1
                        yield digit
                    if padded:
                        for _ in range(32 - emitted):
                            work(1)
                            yield 0
    finally:
        powers.clear()
        pending.clear()
        if observe_workspace is not None:
            observe_workspace(0, 0)


def digits_lsd(value: int, base: int, width: int | None = None) -> tuple[int, ...]:
    """Canonical least-significant-first radix digits with optional zero extension."""
    out = list(iter_digits_lsd(value, base))
    if width is not None:
        width = int(width)
        if width < len(out):
            raise ValueError((width, len(out)))
        out.extend([0] * (width - len(out)))
    return tuple(out)


def reverse_radix_integer(value: int, base: int) -> int:
    """Reverse the canonical radix digits of a nonnegative integer."""
    base = int(base)
    digits = digits_lsd(int(value), base)
    return value_from_lsd_digits(reversed(digits), base)


def reverse_pair_sums(value: int, base: int) -> tuple[int, ...]:
    """Canonical reverse/add pair field ``d[i] + d[-1-i]``."""
    digits = digits_lsd(int(value), int(base))
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


def symbol_runs(values: Sequence[int] | Iterable[int]) -> tuple[tuple[int, int], ...]:
    """Canonical run-length encoding of an integer symbol stream.

    This representation-only primitive is shared by sequence and projection
    compilers so run encoding never becomes duplicated semantic machinery.
    """
    out: list[tuple[int, int]] = []
    for value in values:
        symbol = int(value)
        if out and out[-1][0] == symbol:
            out[-1] = (symbol, out[-1][1] + 1)
        else:
            out.append((symbol, 1))
    return tuple(out)


def periodic_position_bases(length: int, period: Sequence[int]) -> tuple[int, ...]:
    """Canonical least-significant-first radix factors covering ``length``.

    Repeats ``period`` until the represented domain covers ``length``.  When
    the next periodic radix would overshoot but the exact remaining factor is
    a divisor of that radix, the final position is refined to that factor.
    This preserves the periodic coordinate while avoiding gratuitous padding
    such as ``4,2,8,4,2,8`` for a 1024-element domain, which canonically ends
    in ``...,2`` instead.
    """
    length = int(length)
    bases = tuple(map(int, period))
    if length <= 0 or not bases or any(base < 2 for base in bases):
        raise ValueError((length, bases))
    out: list[int] = []
    domain = 1
    index = 0
    while domain < length:
        base = bases[index % len(bases)]
        if length % domain == 0:
            remaining = length // domain
            if 1 < remaining < base and base % remaining == 0:
                base = remaining
        out.append(base)
        domain *= base
        index += 1
    return tuple(out)


def value_from_lsd_digits(digits: Sequence[int] | Iterable[int], base: int) -> int:
    """Evaluate an LSF radix word without imposing a canonical width."""
    base = int(base)
    if base < 2:
        raise ValueError(base)
    # Each retained block represents a contiguous LSF word. Equal-width
    # blocks combine chronologically; the explicit stack has logarithmic
    # depth and never grows an endpoint integer once per input digit.
    blocks: list[tuple[int, int, int]] = []
    part, weight, size = 0, 1, 0
    for digit in digits:
        digit = int(digit)
        if not 0 <= digit < base:
            raise ValueError((digit, base))
        part += digit * weight
        weight *= base
        size += 1
        if size == 32:
            while blocks and blocks[-1][2] == size:
                low, low_weight, low_size = blocks.pop()
                part = low + low_weight * part
                weight *= low_weight
                size += low_size
            blocks.append((part, weight, size))
            part, weight, size = 0, 1, 0
    out = part
    for low, low_weight, _ in reversed(blocks):
        out = low + low_weight * out
    return out


__all__ = [
    "bit_width",
    "digit_threshold_mask",
    "digits_lsd",
    "periodic_position_bases",
    "reverse_pair_sums",
    "reverse_radix_integer",
    "symbol_runs",
    "value_from_lsd_digits",
]
