"""Small integer-to-symmetric-pair encoding shared by benchmark probes."""

from __future__ import annotations


def pair_from_int(value: int, base: int = 10) -> tuple[int, ...]:
    """Return least-significant-first digit sums with their mirror positions."""
    digits: list[int] = []
    n = int(value)
    while n:
        digits.append(n % base)
        n //= base
    digits = digits or [0]
    return tuple(digits[index] + digits[-1 - index] for index in range(len(digits)))
