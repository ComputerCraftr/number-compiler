"""Residual-language lower bounds for the special-number source bend.

The temporal Fermat/Mersenne quotient is small because its *transition law* is
known and only the target-distance class is needed.  The source bend search is
different.  On one hidden factor q, the affine atom

    1 + C*m

is nonunit exactly at one residue class ``m == -C^-1 (mod q)``.  Under slot
translation ``m -> m+1`` this is a unary Moore machine with exactly q residual
classes: every residue has a different distance to the next pulse.

This module makes that lower bound executable.  It rules out the idea that the
existing finite wreath/radix transducer can discover the source bit merely by
being pointed at the factor-slot dimension.  Supplying q makes the state tiny
(log q bits) and binary-powerable, but q is precisely the hidden factor axis.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from number_compiler.arithmetic.functions.finite_unary import minimize_unary_moore
from number_compiler.sequences.power_numbers.numbers import (
    fermat_factor_stride,
    fermat_number,
    mersenne_factor_stride,
    mersenne_number,
)


@dataclass(frozen=True, slots=True)
class SourceBendResidualAudit:
    family: str
    parameter: int
    prime_factor: int
    stride: int
    bend_residue: int
    exact_residual_classes: int
    state_bits: int
    factor_label_bits: int
    binary_translation_powerable: bool
    factor_axis_supplied: bool
    source_injection_closed: bool


@dataclass(frozen=True, slots=True)
class SourceBendGlobalLowerBound:
    family: str
    parameter: int
    supplied_factors: tuple[int, ...]
    largest_local_residual_classes: int
    lower_bound_state_bits: int
    complete_factorization: bool
    factor_truth_only: bool = True


def _modulus_and_stride(family: str, parameter: int) -> tuple[int, int]:
    family, parameter = str(family), int(parameter)
    if family == "fermat":
        return fermat_number(parameter), fermat_factor_stride(parameter)
    if family == "mersenne":
        return mersenne_number(parameter), mersenne_factor_stride(parameter)
    raise ValueError(family)


def source_bend_residual_audit(
    family: str,
    parameter: int,
    supplied_prime_factor: int,
    *,
    enumerate_limit: int = 10_000,
) -> SourceBendResidualAudit:
    """Return the exact q-class local bend observer, optionally minimizing it."""
    N, stride = _modulus_and_stride(family, parameter)
    q = int(supplied_prime_factor)
    if q <= 2 or N % q or gcd(stride, q) != 1:
        raise ValueError((family, parameter, q, stride))
    bend = (-pow(stride, -1, q)) % q

    # The theorem gives q classes for every q.  For bounded q independently
    # verify it with the repository's exact Moore minimizer.
    if q <= int(enumerate_limit):
        transition = tuple((state + 1) % q for state in range(q))
        outputs = tuple(state == bend for state in range(q))
        minimized = minimize_unary_moore(transition, outputs)
        if minimized.classes != q:
            raise AssertionError((q, bend, minimized.classes))

    return SourceBendResidualAudit(
        str(family),
        int(parameter),
        q,
        stride,
        bend,
        q,
        max(1, (q - 1).bit_length()),
        q.bit_length(),
        True,
        True,
        False,
    )


def source_bend_global_lower_bound(
    family: str,
    parameter: int,
    supplied_factors: tuple[int, ...],
) -> SourceBendGlobalLowerBound:
    N, _ = _modulus_and_stride(family, parameter)
    factors = tuple(map(int, supplied_factors))
    if not factors or any(q <= 2 or N % q for q in factors):
        raise ValueError((family, parameter, factors))
    largest = max(factors)
    product = 1
    for q in factors:
        product *= q
    return SourceBendGlobalLowerBound(
        str(family),
        int(parameter),
        factors,
        largest,
        max(1, (largest - 1).bit_length()),
        product == N,
        True,
    )


__all__ = [
    "SourceBendGlobalLowerBound",
    "SourceBendResidualAudit",
    "source_bend_global_lower_bound",
    "source_bend_residual_audit",
]
