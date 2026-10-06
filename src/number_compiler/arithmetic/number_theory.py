"""Small exact number-theory operations used by algebraic owners.

These helpers contain no prime-sequence state or enumeration.  Keeping their
implementation in arithmetic lets cyclotomic and residue code depend on the
mathematics without depending on the prime family compiler.
"""

from __future__ import annotations

from math import isqrt


def normalize_jacobi_inputs(a: int, n: int) -> tuple[int, int]:
    a = int(a)
    n = int(n)
    if n <= 0 or not (n & 1):
        raise ValueError((a, n))
    return a, n


def jacobi_symbol(a: int, n: int) -> int:
    """Return the exact Jacobi symbol ``(a/n)`` for positive odd ``n``."""
    a, n = normalize_jacobi_inputs(a, n)
    a %= n
    result = 1
    while a:
        while not (a & 1):
            a >>= 1
            if n & 7 in (3, 5):
                result = -result
        a, n = n, a
        if (a & 3) == 3 and (n & 3) == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def smallest_factor(n: int, *, max_divisor: int | None = None) -> int | None:
    """Return the least proper factor, or ``None`` if no factor was found.

    With ``max_divisor``, ``None`` means that no factor within the bound was
    found; it is not an unrestricted primality claim.
    """
    n = int(n)
    if n < 2 or n == 2:
        return None
    if n % 2 == 0:
        return 2
    limit = isqrt(n)
    if max_divisor is not None:
        if type(max_divisor) is not int or max_divisor < 2:
            raise ValueError("trial divisor bound must be at least two")
        limit = min(limit, max_divisor)
    for factor in range(3, limit + 1, 2):
        if n % factor == 0:
            return factor
    return None


def is_prime_u64(value: int) -> bool:
    """Deterministic primality predicate for unsigned 64-bit integers."""
    n = int(value)
    if n < 2 or n >= 1 << 64:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for prime in small:
        if n == prime:
            return True
        if n % prime == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for base in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        a = base % n
        if a == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


__all__ = [
    "is_prime_u64",
    "jacobi_symbol",
    "normalize_jacobi_inputs",
    "smallest_factor",
]
