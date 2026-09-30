"""Exact prime-power binomial transport for carry-event algebra.

Reverse-and-add pair coefficients in base ``b`` are recovered from
``w=bit_length(2b-2)`` bit planes, so event transport only needs binomial
coefficients modulo ``2**w``.  This module evaluates those coefficients from the
binary digits of ``n``/``k`` without constructing the (potentially enormous)
integer ``binom(n,k)``.

For ``m = 2**a`` write ``n! = 2**v2(n!) * u(n)`` with ``u(n)`` odd.  The odd
factorial satisfies

    u(n) = product_{1<=j<=n, j odd} j * u(floor(n/2))  (mod m),

and the odd product is periodic modulo ``m``. The implementation first builds
and caches ``2**a + 1`` prefix entries; only subsequent queries reuse that
table while traversing the binary digits of ``n``. This is useful at fixed
small precision, not a polynomial-in-``a`` cold construction.
Kummer/Legendre supplies the exact 2-adic
valuation of ``binom(n,k)``; if it reaches ``a`` the coefficient is zero.

The transport helper exploits the extra factor ``2**q`` directly:
``2**q * binom(r,k) mod 2**w`` needs ``binom(r,k)`` only modulo ``2**(w-q)``.
"""

from __future__ import annotations
from number_compiler.arithmetic.contracts.input_validation import (
    normalized_integer_pair,
)

from functools import cache


def v2_factorial(n: int) -> int:
    n = int(n)
    if n < 0:
        raise ValueError(n)
    # Legendre: v2(n!) = n - popcount(n).
    return n - n.bit_count()


def v2_binomial(n: int, k: int) -> int:
    n, k = int(n), int(k)
    if not 0 <= k <= n:
        raise ValueError((n, k))
    # Equivalent to the number of binary carries in k + (n-k).
    return v2_factorial(n) - v2_factorial(k) - v2_factorial(n - k)


@cache
def _odd_prefix_table(bits: int) -> tuple[tuple[int, ...], int]:
    bits = int(bits)
    if bits <= 0:
        raise ValueError(bits)
    modulus = 1 << bits
    prefix = [1] * (modulus + 1)
    value = 1
    for i in range(1, modulus + 1):
        if i & 1:
            value = (value * i) % modulus
        prefix[i] = value
    return tuple(prefix), value


def odd_factorial_mod_pow2(n: int, bits: int) -> int:
    """Odd part of ``n!``; cold setup allocates ``2**bits + 1`` prefix entries."""
    n, bits = normalized_integer_pair(n, bits, second_minimum=1)
    modulus = 1 << bits
    prefix, block_product = _odd_prefix_table(bits)
    out = 1
    while n:
        blocks, rem = divmod(n, modulus)
        if blocks:
            out = (out * pow(block_product, blocks, modulus)) % modulus
        out = (out * prefix[rem]) % modulus
        n >>= 1
    return out


def binomial_mod_pow2(n: int, k: int, bits: int) -> int:
    """Return ``binom(n,k) mod 2**bits`` without materializing ``binom(n,k)``."""
    n, k, bits = int(n), int(k), int(bits)
    if not 0 <= k <= n or bits <= 0:
        raise ValueError((n, k, bits))
    if k == 0 or k == n:
        return 1 % (1 << bits)
    k = min(k, n - k)
    valuation = v2_binomial(n, k)
    if valuation >= bits:
        return 0
    modulus = 1 << bits
    un = odd_factorial_mod_pow2(n, bits)
    uk = odd_factorial_mod_pow2(k, bits)
    ur = odd_factorial_mod_pow2(n - k, bits)
    odd = un
    odd = (odd * pow(uk, -1, modulus)) % modulus
    odd = (odd * pow(ur, -1, modulus)) % modulus
    return (odd << valuation) & (modulus - 1)


def scaled_binomial_mod_pow2(r: int, k: int, q: int, bits: int) -> int:
    """Return ``2**q * binom(r,k) mod 2**bits`` with early 2-adic death."""
    r, k, q, bits = map(int, (r, k, q, bits))
    if not 0 <= k <= r or q < 0 or bits <= 0:
        raise ValueError((r, k, q, bits))
    if q >= bits:
        return 0
    reduced_bits = bits - q
    return (binomial_mod_pow2(r, k, reduced_bits) << q) & ((1 << bits) - 1)


def transport_kernel_mod_pow2(r: int, q: int, bits: int) -> tuple[int, ...]:
    """Exact coefficient vector for ``2**q * (1+S)**r`` modulo ``2**bits``."""
    r, q, bits = map(int, (r, q, bits))
    if r < 0 or q < 0 or bits <= 0:
        raise ValueError((r, q, bits))
    if q >= bits:
        return (0,) * (r + 1)
    return tuple(scaled_binomial_mod_pow2(r, k, q, bits) for k in range(r + 1))


__all__ = [
    "binomial_mod_pow2",
    "odd_factorial_mod_pow2",
    "scaled_binomial_mod_pow2",
    "transport_kernel_mod_pow2",
    "v2_binomial",
    "v2_factorial",
]
