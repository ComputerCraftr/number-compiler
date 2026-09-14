"""Finite-window binary-automaton diagnostics for the prime Boolean field.

A direct finite automaton on binary digits would identify residue prefixes that
induce the same residual primality language.  These probes count those residual
languages exactly on a bounded tail and charge the sieve used to construct the
finite observation.  They are diagnostics, not a replacement prime projector.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd, isqrt


@dataclass(frozen=True, slots=True)
class PrimeResidualKernelMetrics:
    prefix_bits: int
    tail_bits: int
    odd_prefixes: int
    distinct_residuals: int
    sieve_limit: int
    sieve_updates: int


@dataclass(frozen=True, slots=True)
class BooleanANFMetrics:
    input_bits: int
    degree: int
    terms: int
    terms_by_degree: tuple[tuple[int, int], ...]


@dataclass(frozen=True, slots=True)
class PrimeCyclotomicOrderMetrics:
    limit: int
    generators: int
    odd_generators: int
    exact_order_groups: int
    signed_order_groups: int
    max_exact_group_size: int
    max_signed_group_size: int


@dataclass(frozen=True, slots=True)
class BooleanCoordinateDerivativeMetrics:
    input_bits: int
    derivative_ones: tuple[int, ...]
    pair_counts: tuple[int, ...]
    constant_derivatives: int

    @property
    def densities(self) -> tuple[float, ...]:
        return tuple(
            ones / pairs for ones, pairs in zip(self.derivative_ones, self.pair_counts)
        )


def _order_two_mod_prime(prime: int, *, signed: bool = False) -> int:
    q = int(prime)
    if q <= 2 or q % 2 == 0:
        raise ValueError(q)
    value = 2 % q
    order = 1
    if signed and value == q - 1:
        return order
    while value != 1:
        value = (value * 2) % q
        order += 1
        if signed and value == q - 1:
            return order
    return order


def prime_cyclotomic_order_metrics(limit: int) -> PrimeCyclotomicOrderMetrics:
    """Discover wheel generators and group them by binary cyclotomic order.

    No prime list is supplied: ``k`` is a fresh generator exactly when it is
    coprime to the product of all earlier generators.  For every odd discovered
    prime ``q``, ``ord_q(2)=d`` places it in the cyclotomic value ``Phi_d(2)``.
    The signed order identifies ``+1`` and ``-1`` periods.
    """
    limit = int(limit)
    if limit < 2:
        raise ValueError(limit)
    product = 1
    exact: dict[int, int] = {}
    signed: dict[int, int] = {}
    generators = 0
    odd = 0
    for k in range(2, limit + 1):
        if gcd(k, product) != 1:
            continue
        product *= k
        generators += 1
        if k == 2:
            continue
        odd += 1
        d = _order_two_mod_prime(k)
        sd = _order_two_mod_prime(k, signed=True)
        exact[d] = exact.get(d, 0) + 1
        signed[sd] = signed.get(sd, 0) + 1
    return PrimeCyclotomicOrderMetrics(
        limit,
        generators,
        odd,
        len(exact),
        len(signed),
        max(exact.values(), default=0),
        max(signed.values(), default=0),
    )


def _sieve(limit: int) -> tuple[bytearray, int]:
    limit = int(limit)
    if limit < 1:
        raise ValueError(limit)
    prime = bytearray(b"\x01") * (limit + 1)
    prime[0:2] = b"\x00\x00"
    updates = 0
    for p in range(2, isqrt(limit) + 1):
        if not prime[p]:
            continue
        for q in range(p * p, limit + 1, p):
            updates += 1
            prime[q] = 0
    return prime, updates


def prime_lsb_residual_kernel(
    prefix_bits: int, tail_bits: int
) -> PrimeResidualKernelMetrics:
    """Count residual prime languages after fixing low ``prefix_bits`` bits.

    Only odd prefixes are retained because every nontrivial prime is odd.  A
    residual signature is the Boolean vector

        n -> prime(prefix + 2**prefix_bits * n),  0 <= n < 2**tail_bits.

    A universal finite LSB-first automaton would need to merge these residuals;
    finite-window growth therefore directly measures whether such merging is
    visible before any BDD post-processing.
    """
    e, t = int(prefix_bits), int(tail_bits)
    if e <= 0 or t <= 0:
        raise ValueError((e, t))
    limit = (1 << (e + t)) - 1
    prime, updates = _sieve(limit)
    signatures: set[int] = set()
    for prefix in range(1, 1 << e, 2):
        signature = 0
        for tail in range(1 << t):
            if prime[prefix + (tail << e)]:
                signature |= 1 << tail
        signatures.add(signature)
    return PrimeResidualKernelMetrics(
        e, t, 1 << (e - 1), len(signatures), limit, updates
    )


def boolean_coordinate_derivative_metrics(
    mask: int, input_bits: int
) -> BooleanCoordinateDerivativeMetrics:
    """Measure exact F_2 coordinate derivatives of a finite Boolean block.

    For coordinate ``b`` this compares ``f(j)`` and ``f(j xor 2**b)`` once
    per unordered hypercube edge.  Every coordinate derivative of an affine
    Boolean function is constant, so any interior density immediately rejects
    exact affine structure without relying on a fitted model.
    """
    mask, k = int(mask), int(input_bits)
    if k < 0 or mask < 0 or mask >= (1 << (1 << k)):
        raise ValueError((mask, k))
    size = 1 << k
    derivative_ones: list[int] = []
    pair_counts: list[int] = []
    constant = 0
    for bit in range(k):
        step = 1 << bit
        ones = 0
        pairs = 0
        for j in range(size):
            if j & step:
                continue
            ones += ((mask >> j) ^ (mask >> (j | step))) & 1
            pairs += 1
        derivative_ones.append(ones)
        pair_counts.append(pairs)
        if ones == 0 or ones == pairs:
            constant += 1
    return BooleanCoordinateDerivativeMetrics(
        k, tuple(derivative_ones), tuple(pair_counts), constant
    )


def boolean_anf_metrics(mask: int, input_bits: int) -> BooleanANFMetrics:
    """Return algebraic-normal-form complexity of one ``2**input_bits`` bitmap."""
    mask, k = int(mask), int(input_bits)
    if k < 0 or mask < 0 or mask >= (1 << (1 << k)):
        raise ValueError((mask, k))
    size = 1 << k
    coeff = [(mask >> i) & 1 for i in range(size)]
    # Fast Mobius transform over F_2.
    for bit in range(k):
        step = 1 << bit
        for index in range(size):
            if index & step:
                coeff[index] ^= coeff[index ^ step]
    by_degree: dict[int, int] = {}
    for monomial, present in enumerate(coeff):
        if present:
            degree = monomial.bit_count()
            by_degree[degree] = by_degree.get(degree, 0) + 1
    degree = max(by_degree, default=-1)
    return BooleanANFMetrics(
        k, degree, sum(by_degree.values()), tuple(sorted(by_degree.items()))
    )


__all__ = [
    "BooleanANFMetrics",
    "BooleanCoordinateDerivativeMetrics",
    "PrimeCyclotomicOrderMetrics",
    "PrimeResidualKernelMetrics",
    "boolean_anf_metrics",
    "boolean_coordinate_derivative_metrics",
    "prime_cyclotomic_order_metrics",
    "prime_lsb_residual_kernel",
]
