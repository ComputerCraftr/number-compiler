"""Alternate-radix/mixed-radix diagnostics for prime Boolean morphisms.

This module is analysis-only and is intentionally not imported by the canonical
sequence compiler.  It distinguishes two operations that are easy to conflate:

* *reinterpretation*: keep a binary 0/1 symbol string but change its place
  weights from powers of 2 to powers of another base.  This is an invertible
  coordinate map on the 0/1-digit image, not a primality-preserving arithmetic
  map.
* *mixed-radix conversion*: encode the same integer using a periodic sequence
  of digit bases.  This changes the decision coordinate while preserving the
  arithmetic value.

The finite Boolean residual probe then asks whether prime/composite bits merge
more strongly under those coordinates.  Projection work used to obtain the
finite prime mask is reported, never hidden behind the residual count.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from math import prod

from number_compiler.arithmetic.fields.congruence_automaton import (
    reinterpret_binary_digits,
)
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    periodic_position_bases,
)
from number_compiler.arithmetic.polynomials.cyclotomic import (
    polynomial_divisible_by_cyclotomic,
)
from number_compiler.sequences.prime.set import project_odd_prime_block


@dataclass(frozen=True, slots=True)
class MixedRadixPrimeResidualMetrics:
    start: int
    length: int
    base_period: tuple[int, ...]
    positions: int
    domain_size: int
    padding: int
    residual_counts: tuple[int, ...]
    residual_states_total: int
    max_residual_states: int
    charged_references: int
    charged_description_bits: int
    digit_alphabet_payload_bits: int
    projection_canonical_lanes: int


def mixed_radix_prime_residual_metrics(
    start: int, length: int, base_period: Sequence[int]
) -> MixedRadixPrimeResidualMetrics:
    """Exact finite residual-language counts under an LSF mixed-radix order.

    A third terminal symbol marks padded coordinates outside the requested
    block, preventing padding from being incorrectly merged with composites.
    At depth ``p`` we fix the first ``p`` mixed-radix digits and canonicalize
    the complete residual language over all remaining higher digits.
    """
    start, length = int(start), int(length)
    if start < 3 or not (start & 1) or length <= 0:
        raise ValueError((start, length))
    bases = periodic_position_bases(length, base_period)
    domain = prod(bases)
    projection = project_odd_prime_block(start, length)
    prime_mask = projection.prime_mask
    labels = tuple(
        (1 if ((prime_mask >> j) & 1) else 0) if j < length else 2
        for j in range(domain)
    )
    counts: list[int] = []
    stride = 1
    # depth 0 is the whole language; subsequent depths fix one more low digit.
    for depth in range(len(bases) + 1):
        signatures: set[tuple[int, ...]] = set()
        for prefix in range(stride):
            signatures.add(labels[prefix:domain:stride])
        counts.append(len(signatures))
        if depth < len(bases):
            stride *= bases[depth]
    payload = sum(bit_width(b - 1) for b in bases)
    references = sum(counts[d] * bases[d] for d in range(len(bases)))
    nodes = sum(counts[:-1]) + counts[-1]
    id_bits = bit_width(max(1, nodes))
    description = nodes + references * id_bits + payload
    return MixedRadixPrimeResidualMetrics(
        start,
        length,
        tuple(map(int, base_period)),
        len(bases),
        domain,
        domain - length,
        tuple(counts),
        sum(counts),
        max(counts),
        references,
        description,
        payload,
        len(projection.canonical_lanes),
    )


@dataclass(frozen=True, slots=True)
class ReinterpretedPrimeCyclotomicMetrics:
    start: int
    length: int
    target_base: int
    moduli: tuple[int, ...]
    modulus_bits: int
    classes: int
    ambiguous_classes: int
    ambiguous_candidates: int
    pure_prime_classes: int
    pure_composite_classes: int
    largest_class: int
    projection_canonical_lanes: int


def reinterpreted_prime_cyclotomic_metrics(
    start: int, length: int, target_base: int
) -> ReinterpretedPrimeCyclotomicMetrics:
    """Group prime labels by cyclotomic residues of reinterpreted binary words."""
    start, length, target_base = int(start), int(length), int(target_base)
    if start < 3 or not (start & 1) or length <= 0 or target_base < 2:
        raise ValueError((start, length, target_base))
    projection = project_odd_prime_block(start, length)
    # Power-of-two +/- channels, deduplicated; omit modulus 1.
    mods: list[int] = []
    for m in (1, 2, 4):
        for modulus in (pow(target_base, m) - 1, pow(target_base, m) + 1):
            if modulus > 1 and modulus not in mods:
                mods.append(modulus)
    groups: dict[tuple[int, ...], list[int]] = {}
    for j in range(length):
        n = start + 2 * j
        encoded = reinterpret_binary_digits(n, target_base)
        key = tuple(encoded % m for m in mods)
        label = (projection.prime_mask >> j) & 1
        slot = groups.setdefault(key, [0, 0, 0])
        slot[label] += 1
        slot[2] += 1
    ambiguous = ambiguous_candidates = pure_prime = pure_composite = largest = 0
    for composite, prime, total in groups.values():
        largest = max(largest, total)
        if composite and prime:
            ambiguous += 1
            ambiguous_candidates += total
        elif prime:
            pure_prime += 1
        else:
            pure_composite += 1
    return ReinterpretedPrimeCyclotomicMetrics(
        start,
        length,
        target_base,
        tuple(mods),
        sum(bit_width(m) for m in mods),
        len(groups),
        ambiguous,
        ambiguous_candidates,
        pure_prime,
        pure_composite,
        largest,
        len(projection.canonical_lanes),
    )


@dataclass(frozen=True, slots=True)
class BinaryDigitCyclotomicMetrics:
    value: int
    bit_length: int
    tested_orders: int
    cyclotomic_orders: tuple[int, ...]


def binary_digit_cyclotomic_metrics(
    value: int, *, max_order: int = 64
) -> BinaryDigitCyclotomicMetrics:
    """Factor the 0/1 digit polynomial structurally, not the integer value.

    If ``B_n(z)=sum bit_i z^i`` has ``Phi_m(z)`` as an integer-polynomial
    factor, reinterpreting the same bit string in *any* radix ``b`` carries the
    corresponding factor ``Phi_m(b)``.  Mersenne/Fermat words are the canonical
    pure examples; ordinary prime bit strings are tested without assuming such
    structure.
    """
    value, max_order = int(value), int(max_order)
    if value <= 0 or max_order < 1:
        raise ValueError((value, max_order))
    coeff = tuple(digits_lsd(value, 2))
    orders = tuple(
        m
        for m in range(2, max_order + 1)
        if polynomial_divisible_by_cyclotomic(coeff, m)
    )
    return BinaryDigitCyclotomicMetrics(value, len(coeff), max_order - 1, orders)


__all__ = [
    "BinaryDigitCyclotomicMetrics",
    "MixedRadixPrimeResidualMetrics",
    "ReinterpretedPrimeCyclotomicMetrics",
    "binary_digit_cyclotomic_metrics",
    "mixed_radix_prime_residual_metrics",
    "reinterpreted_prime_cyclotomic_metrics",
]
