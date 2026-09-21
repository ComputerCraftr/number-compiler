"""Canonical small radix utilities shared by every sequence compiler.

These helpers are intentionally representation-only.  They never perform a
sequence transition and therefore cannot become a parallel semantic state.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence


def bit_width(value: int) -> int:
    """Return at least one bit for a nonnegative integer magnitude."""
    value = int(value)
    if value < 0:
        value = -value
    return max(1, value.bit_length())


def digits_lsd(value: int, base: int, width: int | None = None) -> tuple[int, ...]:
    """Canonical least-significant-first radix digits with optional zero extension."""
    value, base = int(value), int(base)
    if value < 0 or base < 2:
        raise ValueError((value, base))
    out: list[int] = []
    if value < base:
        out.append(value)
    elif base & (base - 1) == 0:
        digit_bits = base.bit_length() - 1
        accumulator = available = 0
        for byte in value.to_bytes((value.bit_length() + 7) // 8, "little"):
            accumulator |= byte << available
            available += 8
            while available >= digit_bits:
                out.append(accumulator & (base - 1))
                accumulator >>= digit_bits
                available -= digit_bits
        if available:
            out.append(accumulator)
        while len(out) > 1 and out[-1] == 0:
            out.pop()
    else:
        # Split at radix powers before extracting bounded leaves. A digit
        # extraction never divides the entire remaining endpoint integer.
        powers = [base**32]
        while powers[-1] <= value:
            powers.append(powers[-1] * powers[-1])
        pending = [(value, len(powers) - 1, False)]
        while pending:
            part, level, padded = pending.pop()
            if level:
                high, low = divmod(part, powers[level - 1])
                if high or padded:
                    pending.append((high, level - 1, padded))
                    pending.append((low, level - 1, True))
                else:
                    pending.append((low, level - 1, False))
            else:
                start = len(out)
                while part:
                    part, digit = divmod(part, base)
                    out.append(digit)
                if padded:
                    out.extend([0] * (32 - (len(out) - start)))
    if not out:
        out.append(0)
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
    "digits_lsd",
    "periodic_position_bases",
    "reverse_pair_sums",
    "reverse_radix_integer",
    "symbol_runs",
    "value_from_lsd_digits",
]
