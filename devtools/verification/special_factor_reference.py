"""Cyclotomic factor-witness morphisms for Fermat and Mersenne families.

These maps deliberately separate *testing a supplied factor witness* from
searching for one.  The witness tests exploit the exponent coordinate directly:

* q | F_n iff 2**(2**n) == -1 (mod q), requiring n modular squarings;
* q | M_p iff 2**p == 1 (mod q), requiring O(log p) binary compositions.

The familiar factor congruence classes are retained as an independent set-map
filter.  A bounded prefix search may also be collapsed into one balanced candidate
product by ``batched_special_factor_witness``; its product construction and gcd
descent are explicitly metered, and window exhaustion remains ``unknown``.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from number_compiler.arithmetic.fields.morphism_core import (
    QuadraticPower,
    modular_power,
)
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.fields.symbolic_extent import (
    DyadicExtent,
    Extent,
    extent_description_bits,
)


@dataclass(frozen=True, slots=True)
class ModularPowerWitness:
    family: str
    parameter: int
    candidate_factor: int
    exponent: Extent
    residue: int
    target: int
    compositions: int
    stride_compatible: bool

    @property
    def divides(self) -> bool:
        return self.residue == self.target

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "modular-power-witness",
            self.family,
            self.parameter,
            self.candidate_factor,
            self.exponent,
            self.residue,
            self.target,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.parameter)
            + bit_width(self.candidate_factor)
            + extent_description_bits(self.exponent)
            + bit_width(self.residue)
            + bit_width(self.target)
            + bit_width(self.compositions)
        )


@dataclass(frozen=True, slots=True)
class BatchedSpecialFactorWitness:
    """One exact set-product witness over an admissible factor-slot window.

    The candidate identities are used only while building a balanced product
    tree.  The expensive special exponent is evaluated once modulo the product
    of the complete window.  A nontrivial gcd is then descended through that
    tree to one concrete proper divisor.  This shares the powered arithmetic
    across candidates instead of replaying it once per slot.

    Exhausting a finite window proves nothing about primality.
    """

    family: str
    parameter: int
    candidate_count: int
    candidate_product_bits: int
    product_multiplications: int
    product_depth: int
    powered_compositions: int
    gcd_calls: int
    gcd_value: int
    proper_factor: int | None
    witness_k: int | None

    @property
    def composite_witness(self) -> bool:
        return self.proper_factor is not None

    @property
    def description_bits(self) -> int:
        return sum(
            bit_width(abs(value))
            for value in (
                self.parameter,
                self.candidate_count,
                self.candidate_product_bits,
                self.product_multiplications,
                self.product_depth,
                self.powered_compositions,
                self.gcd_calls,
                self.gcd_value,
                self.proper_factor or 0,
                self.witness_k or 0,
            )
        )


def _balanced_product_levels(
    values: tuple[int, ...],
) -> tuple[tuple[tuple[int, ...], ...], int]:
    """Return leaf-to-root balanced product levels and multiplication count."""
    if not values:
        return (), 0
    levels: list[tuple[int, ...]] = [tuple(map(int, values))]
    multiplications = 0
    while len(levels[-1]) > 1:
        current = levels[-1]
        nxt: list[int] = []
        for index in range(0, len(current), 2):
            if index + 1 == len(current):
                nxt.append(current[index])
            else:
                nxt.append(current[index] * current[index + 1])
                multiplications += 1
        levels.append(tuple(nxt))
    return tuple(levels), multiplications


def _descend_product_gcd(
    residue: int,
    levels: tuple[tuple[int, ...], ...],
) -> tuple[int | None, int | None, int]:
    """Find one leaf divisor using gcds only; return (leaf,index,gcd_calls)."""
    if not levels:
        return None, None, 0
    index = 0
    gcd_calls = 0
    for level in range(len(levels) - 2, -1, -1):
        left_index = index * 2
        current = levels[level]
        left = current[left_index]
        left_gcd = gcd(int(residue), left)
        gcd_calls += 1
        if left_gcd > 1:
            index = left_index
            continue
        right_index = left_index + 1
        if right_index >= len(current):
            return None, None, gcd_calls
        right = current[right_index]
        right_gcd = gcd(int(residue), right)
        gcd_calls += 1
        if right_gcd <= 1:
            return None, None, gcd_calls
        index = right_index
    leaf = levels[0][index]
    return leaf, index, gcd_calls


def batched_special_factor_witness(
    family: str,
    parameter: int,
    candidate_count: int,
) -> BatchedSpecialFactorWitness:
    """Test one prefix of special-form factor slots with shared powering.

    Fermat slots are ``q_k = 1 + k*2**(n+2)``.  Mersenne slots are
    ``q_k = 1 + 2*p*k``.  Every candidate is strictly smaller than the special
    number; if the candidate product has nontrivial gcd with that number, the
    product tree yields a proper divisor.  No factorization of the special
    number is performed.
    """
    family = str(family)
    parameter = int(parameter)
    candidate_count = int(candidate_count)
    if candidate_count < 0:
        raise ValueError(candidate_count)
    if family == "fermat":
        if parameter < 0:
            raise ValueError(parameter)
        height = 1 << parameter
        modulus_bits = height + 1
        stride = 1 << (parameter + 2)
    elif family == "mersenne":
        if parameter < 2:
            raise ValueError(parameter)
        modulus_bits = parameter
        stride = 2 * parameter
    else:
        raise ValueError(family)

    candidates: list[int] = []
    slot_ids: list[int] = []
    # Avoid materializing the special number merely to bound the window: a
    # candidate with fewer bits is certainly smaller.  Equality/edge cases are
    # resolved exactly for the tiny boundary where the candidate bit length is
    # not decisive.
    for k in range(1, candidate_count + 1):
        q = stride * k + 1
        q_bits = bit_width(q)
        if q_bits > modulus_bits:
            break
        if q_bits == modulus_bits:
            special = (
                ((1 << (1 << parameter)) + 1)
                if family == "fermat"
                else ((1 << parameter) - 1)
            )
            if q >= special:
                break
        candidates.append(q)
        slot_ids.append(k)
    if not candidates:
        return BatchedSpecialFactorWitness(
            family,
            parameter,
            0,
            0,
            0,
            0,
            0,
            0,
            1,
            None,
            None,
        )

    levels, product_multiplies = _balanced_product_levels(tuple(candidates))
    product = levels[-1][0]
    if family == "fermat":
        residue = QuadraticPower(parameter).apply_multiplicative(2, product)
        powered = parameter
        residue = (residue + 1) % product
    else:
        powered_result = modular_power(2, parameter, product)
        residue = (powered_result.value - 1) % product
        powered = powered_result.compositions

    common = gcd(residue, product)
    gcd_calls = 1
    proper = witness_k = None
    if common > 1:
        leaf, leaf_index, descent_calls = _descend_product_gcd(residue, levels)
        gcd_calls += descent_calls
        if leaf is not None and leaf_index is not None:
            # A terminal leaf is one tested factor slot.  It may itself divide
            # the special number, or (if composite) merely contain a common
            # factor; the final gcd distinguishes those two exact cases.
            leaf_gcd = gcd(residue, leaf)
            gcd_calls += 1
            if leaf_gcd == leaf:
                proper = leaf
                witness_k = slot_ids[leaf_index]
            elif leaf_gcd > 1:
                proper = leaf_gcd
                witness_k = slot_ids[leaf_index]
    return BatchedSpecialFactorWitness(
        family,
        parameter,
        len(candidates),
        bit_width(product),
        product_multiplies,
        max(0, len(levels) - 1),
        powered,
        gcd_calls,
        common,
        proper,
        witness_k,
    )


def fermat_factor_witness(index: int, candidate_factor: int) -> ModularPowerWitness:
    n, q = int(index), int(candidate_factor)
    if n < 0 or q <= 2 or not (q & 1):
        raise ValueError((n, q))
    # Start at exponent 1 and double it n times by modular squaring.
    residue = 2 % q
    for _ in range(n):
        residue = residue * residue % q
    exponent = DyadicExtent(n)
    target = (q - 1) % q
    # Every prime factor of F_n for n>1 has v2(q-1) >= n+2.  Test that
    # valuation directly instead of constructing the exponentially large
    # stride 2**(n+2) merely for one divisibility predicate.
    q_minus_one = q - 1
    stride_v2 = (q_minus_one & -q_minus_one).bit_length() - 1
    compatible = True if n <= 1 else stride_v2 >= n + 2
    return ModularPowerWitness(
        "fermat",
        n,
        q,
        exponent,
        residue,
        target,
        n,
        compatible,
    )


def mersenne_factor_witness(
    exponent: int, candidate_factor: int
) -> ModularPowerWitness:
    p, q = int(exponent), int(candidate_factor)
    if p < 2 or q <= 2 or not (q & 1):
        raise ValueError((p, q))
    # Binary exponentiation is the powered multiplicative monoid.  Count only
    # actual modular multiply/square compositions used by this construction.
    powered = modular_power(2, p, q)
    result = powered.value
    compositions = powered.compositions
    # For prime exponent p, every prime divisor q of M_p has q == 1 (mod 2p).
    compatible = (q - 1) % (2 * p) == 0
    return ModularPowerWitness(
        "mersenne",
        p,
        q,
        p,
        result,
        1 % q,
        compositions,
        compatible,
    )


__all__ = [
    "BatchedSpecialFactorWitness",
    "ModularPowerWitness",
    "batched_special_factor_witness",
    "fermat_factor_witness",
    "mersenne_factor_witness",
]
