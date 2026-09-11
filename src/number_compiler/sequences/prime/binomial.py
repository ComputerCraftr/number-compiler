"""Exact Pascal/binomial representation of the prime/composite set.

For ``n >= 2`` one has

    n is prime  <=>  k divides binom(n-1,k-1) for every 2 <= k <= sqrt(n).

A composite ``n`` is witnessed by its smallest prime divisor ``p`` because
``binom(n-1,p-1) == 1 (mod p)``.  Translation in ``n`` is Pascal transport:
rows of ``(1+x)^n`` evolve by the same ``(I+S)^h`` binomial operator used by the
reverse-and-add event algebra.

This is an independent exact set representation.  Canonicalizing its witness
lanes again exposes prime periods; it does not claim a compact projection.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb, gcd, isqrt
from typing import Sequence

from number_compiler.arithmetic.polynomials.binomial_pow2 import binomial_mod_pow2


def pascal_row_prefix(n: int, width: int) -> tuple[int, ...]:
    n, width = int(n), int(width)
    if n < 0 or width < 0:
        raise ValueError((n, width))
    return tuple(comb(n, k) if k <= n else 0 for k in range(width))


def translate_pascal_row_prefix(row: Sequence[int], shift: int) -> tuple[int, ...]:
    """Apply exact ``(I+S)^shift`` to a finite Pascal row prefix."""
    shift = int(shift)
    if shift < 0:
        raise ValueError(shift)
    src = tuple(map(int, row))
    out = []
    for k in range(len(src)):
        out.append(sum(comb(shift, i) * src[k - i] for i in range(k + 1)))
    return tuple(out)


def translate_pascal_row_prefix_mod_pow2(
    row: Sequence[int], shift: int, bits: int
) -> tuple[int, ...]:
    """Bounded 2-adic Pascal transport without materializing huge coefficients."""
    shift, bits = int(shift), int(bits)
    if shift < 0 or bits <= 0:
        raise ValueError((shift, bits))
    modulus = 1 << bits
    src = tuple(int(v) % modulus for v in row)
    coeff = tuple(binomial_mod_pow2(shift, i, bits) for i in range(len(src)))
    return tuple(
        sum(coeff[i] * src[k - i] for i in range(k + 1)) % modulus
        for k in range(len(src))
    )


def binomial_composite_witness(n: int, k: int) -> bool:
    """Whether row index ``k`` proves ``n`` composite."""
    n, k = int(n), int(k)
    if n < 2 or not 2 <= k <= n:
        raise ValueError((n, k))
    return comb(n - 1, k - 1) % k != 0


def binomial_composite(n: int) -> bool:
    n = int(n)
    if n < 4:
        return False
    return any(binomial_composite_witness(n, k) for k in range(2, isqrt(n) + 1))


def witness_requires_shared_factor(n: int, k: int) -> bool:
    """Check the exact containment theorem ``W_k subseteq {gcd(n,k)>1}``.

    The theorem follows from ``n/gcd(n,k) | binom(n,k)``.  This function is a
    convenient executable assertion for differential/adversarial tests.
    """
    return (not binomial_composite_witness(n, k)) or gcd(n, k) > 1


@dataclass(frozen=True, slots=True)
class BinomialWitnessLane:
    k: int
    mask: int
    hits: int
    novel_hits: int


@dataclass(frozen=True, slots=True)
class BinomialPrimeProjection:
    start: int
    length: int
    stride: int
    kmax: int
    composite_mask: int
    natural_witness_lanes: int
    canonical_lanes: tuple[BinomialWitnessLane, ...]


def project_binomial_prime_block(
    start: int,
    length: int,
    *,
    stride: int = 2,
    kmax: int | None = None,
) -> BinomialPrimeProjection:
    """Research-size exact projection through Pascal witness lanes.

    This intentionally evaluates the binomial definition directly.  It is for
    comparing semantic lane quotients on modest blocks, not a fast prime sieve.
    """
    start, length, stride = int(start), int(length), int(stride)
    if start < 2 or length < 0 or stride <= 0:
        raise ValueError((start, length, stride))
    if length == 0:
        return BinomialPrimeProjection(start, 0, stride, 1, 0, 0, ())
    high = start + stride * (length - 1)
    limit = isqrt(high) if kmax is None else min(int(kmax), isqrt(high))
    if limit < 1:
        limit = 1
    covered = 0
    natural = 0
    kept: list[BinomialWitnessLane] = []
    for k in range(2, limit + 1):
        mask = 0
        for j in range(length):
            n = start + stride * j
            if k <= n and binomial_composite_witness(n, k):
                mask |= 1 << j
        if not mask:
            continue
        natural += 1
        novel = mask & ~covered
        if novel:
            kept.append(
                BinomialWitnessLane(k, mask, mask.bit_count(), novel.bit_count())
            )
            covered |= mask
    return BinomialPrimeProjection(
        start, length, stride, limit, covered, natural, tuple(kept)
    )


__all__ = [
    "pascal_row_prefix",
    "translate_pascal_row_prefix",
    "translate_pascal_row_prefix_mod_pow2",
    "binomial_composite_witness",
    "binomial_composite",
    "witness_requires_shared_factor",
    "BinomialWitnessLane",
    "BinomialPrimeProjection",
    "project_binomial_prime_block",
]
