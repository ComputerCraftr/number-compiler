"""Exact pair-field, carry-monoid, and valuation quotients for Collatz.

The odd physical step ``3*n+1`` in radix ``b`` can be compiled from the raw
per-digit field ``3*d_i + [i=0]``.  For decimal digits after the LSD, carry is
always in ``{0,1,2}`` and the digit transfer functions close to a five-element
monoid.  This is the direct spatial analogue of reverse-and-add's carry monoid.

The accelerated odd map supplies the complementary temporal quotient: the nested
sets ``2**k | 3*n+1`` canonicalize to their maximal winner ``v2(3*n+1)``.  The
valuation sequence is exactly a run-length encoding of the parity coordinate.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.carry.collatz_carry_wires import (
    collatz_digit_carry_wires,
)
from number_compiler.arithmetic.contracts.input_validation import (
    normalized_integer_pair,
)
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle, binary_power
from number_compiler.arithmetic.fields.radix import bit_width, digits_lsd
from number_compiler.arithmetic.fields.two_adic import v2_positive as v2
from number_compiler.sequences.collatz.parity import CollatzParitySlab


@dataclass(frozen=True, slots=True)
class Mul3CarryFn:
    """Function on the reachable post-LSD carry alphabet ``{0,1,2}``."""

    outputs: tuple[int, int, int]

    def __post_init__(self) -> None:
        if len(self.outputs) != 3 or any(not 0 <= int(x) <= 2 for x in self.outputs):
            raise ValueError(self.outputs)

    def __call__(self, carry: int) -> int:
        carry = int(carry)
        if carry not in (0, 1, 2):
            raise ValueError(carry)
        return int(self.outputs[carry])

    def after(self, before: Mul3CarryFn) -> Mul3CarryFn:
        """Return ``self o before``."""
        return Mul3CarryFn((self(before(0)), self(before(1)), self(before(2))))


def mul3_digit_carry_fn(digit: int, *, base: int = 10) -> Mul3CarryFn:
    if type(digit) is not int or type(base) is not int:
        raise TypeError("multiply-by-three carry requires exact integers")
    if base < 3 or not 0 <= digit < base:
        raise ValueError((digit, base))
    if base >= 4 and base % 3 == 1:
        return Mul3CarryFn(collatz_digit_carry_wires(digit, base=base).outputs)
    outputs = tuple((3 * digit + carry) // base for carry in range(3))
    if any(x > 2 for x in outputs):
        raise ValueError("post-LSD multiply-by-3 carry escaped {0,1,2}")
    return Mul3CarryFn((outputs[0], outputs[1], outputs[2]))


def mul3_carry_monoid(base: int = 10) -> tuple[Mul3CarryFn, ...]:
    """Synthesize the exact carry-transfer monoid from the radix alphabet.

    The monoid is derived from ``digit -> floor((3*digit+carry)/base)`` and is
    therefore compiler metadata, not retained per-number state.  For every
    tested radix >= 4 its closure is the same five transfer functions.
    """
    if type(base) is not int:
        raise TypeError("multiply-by-three carry radix requires an exact integer")
    if base < 3:
        raise ValueError(base)
    if base >= 4 and base % 3 == 1:
        # These are the five nonempty interval actions.  The empty interval's
        # (0, 1, 2) identity is deliberately separate.
        return tuple(
            Mul3CarryFn(outputs)
            for outputs in (
                (0, 0, 0),
                (0, 1, 1),
                (1, 1, 1),
                (1, 1, 2),
                (2, 2, 2),
            )
        )
    generators = {mul3_digit_carry_fn(d, base=base) for d in range(base)}
    closure = set(generators)
    changed = True
    while changed:
        changed = False
        for a in tuple(closure):
            for b in tuple(closure):
                c = a.after(b)
                if c not in closure:
                    closure.add(c)
                    changed = True
    return tuple(sorted(closure, key=lambda f: f.outputs))


@dataclass(frozen=True, slots=True)
class CollatzValuationStep:
    source: int
    valuation: int
    target: int


def accelerated_odd_collatz(value: int) -> CollatzValuationStep:
    value = int(value)
    if value <= 0 or not (value & 1):
        raise ValueError("accelerated odd Collatz requires a positive odd source")
    m = 3 * value + 1
    valuation = v2(m)
    target = m >> valuation
    if not (target & 1):
        raise AssertionError((value, valuation, target))
    return CollatzValuationStep(value, valuation, target)


def collatz_valuation_itinerary(
    seed: int, *, max_odd_steps: int = 10000
) -> tuple[int, ...]:
    seed, max_odd_steps = normalized_integer_pair(seed, max_odd_steps, first_minimum=1)
    value = seed
    while value > 1 and not (value & 1):
        value //= 2
    out: list[int] = []
    for _ in range(max_odd_steps):
        if value == 1:
            break
        step = accelerated_odd_collatz(value)
        out.append(step.valuation)
        value = step.target
    return tuple(out)


@dataclass(frozen=True, slots=True)
class CollatzValuationProjectionBlock:
    """Exact block monoid of accelerated Collatz valuation projections.

    A symbol ``k`` denotes the complete odd-step action ``(3*x+1)/2**k``.
    Concatenation therefore closes in the existing native parity slab; no
    parity word or multiply/divide carry vector is retained.
    """

    odd_steps: int
    valuation_sum: int
    slab: CollatzParitySlab
    compositions: int = 0

    def __post_init__(self) -> None:
        if self.odd_steps < 0 or self.valuation_sum < 0 or self.compositions < 0:
            raise ValueError(self)
        if self.slab.ones != self.odd_steps or self.slab.width != self.valuation_sum:
            raise ValueError("valuation summary disagrees with slab")

    @classmethod
    def identity(cls) -> CollatzValuationProjectionBlock:
        return cls(0, 0, CollatzParitySlab.identity(), 0)

    @classmethod
    def symbol(cls, valuation: int) -> CollatzValuationProjectionBlock:
        k = int(valuation)
        if k <= 0:
            raise ValueError(k)
        return cls(1, k, CollatzParitySlab(k, 1, 1), 0)

    def then(
        self, other: CollatzValuationProjectionBlock
    ) -> CollatzValuationProjectionBlock:
        return CollatzValuationProjectionBlock(
            self.odd_steps + other.odd_steps,
            self.valuation_sum + other.valuation_sum,
            self.slab.then(other.slab),
            self.compositions + other.compositions + 1,
        )

    def power_block(self, exponent: int) -> CollatzValuationProjectionBlock:
        powered = binary_power(
            self,
            exponent,
            identity=CollatzValuationProjectionBlock.identity(),
            compose=CollatzValuationProjectionBlock.then,
        )
        result = powered.value
        return CollatzValuationProjectionBlock(
            result.odd_steps, result.valuation_sum, result.slab, powered.compositions
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "collatz-valuation-projection",
            self.odd_steps,
            self.valuation_sum,
            self.slab.width,
            self.slab.ones,
            self.slab.offset,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.odd_steps)
            + bit_width(self.valuation_sum)
            + self.slab.description_bits
        )


def valuation_projection_from_runs(
    runs: Sequence[tuple[int, int]],
) -> CollatzValuationProjectionBlock:
    out = CollatzValuationProjectionBlock.identity()
    for valuation, count in runs:
        count = int(count)
        if count < 0:
            raise ValueError(count)
        if count:
            out = out.then(
                CollatzValuationProjectionBlock.symbol(int(valuation)).power_block(
                    count
                )
            )
    return out


def valuation_itinerary_slab(valuations: Sequence[int]) -> CollatzParitySlab:
    """Compose accelerated odd steps without materializing parity bits.

    An odd step of valuation ``v`` is exactly ``(3*x+1)/2**v``, hence the
    parity slab atom ``(width=v, ones=1, offset=1)``.  Composition retains one
    affine/domain object for the whole valuation itinerary.
    """
    slab = CollatzParitySlab.identity()
    for valuation in map(int, valuations):
        if valuation <= 0:
            raise ValueError(valuation)
        slab = slab.then(CollatzParitySlab(valuation, 1, 1))
    return slab


@dataclass(frozen=True, slots=True)
class CollatzAffineResidue:
    """Finite odd-modulus affine projection of one parity/valuation slab."""

    modulus: int
    multiplier: int
    offset: int

    def __post_init__(self) -> None:
        if self.modulus <= 1 or self.modulus % 2 == 0:
            raise ValueError(self.modulus)
        object.__setattr__(self, "multiplier", int(self.multiplier) % self.modulus)
        object.__setattr__(self, "offset", int(self.offset) % self.modulus)

    @property
    def cocycle(self) -> AffineCocycle[int]:
        return AffineCocycle(self.multiplier, self.offset)

    def apply(self, value: int) -> int:
        modulus = self.modulus
        return self.cocycle.apply(
            int(value),
            multiply=lambda a, b: (a * b) % modulus,
            add=lambda a, b: (a + b) % modulus,
        )

    def then(self, other: CollatzAffineResidue) -> CollatzAffineResidue:
        if self.modulus != other.modulus:
            raise ValueError((self.modulus, other.modulus))
        m = self.modulus
        cocycle = self.cocycle.then(
            other.cocycle,
            multiply=lambda a, b: (a * b) % m,
            add=lambda a, b: (a + b) % m,
        )
        return CollatzAffineResidue(m, cocycle.multiplier, cocycle.addend)


def collatz_slab_mod_odd(slab: CollatzParitySlab, modulus: int) -> CollatzAffineResidue:
    """Project an exact Collatz slab to one constant-size odd-modulus affine map."""
    modulus = int(modulus)
    if modulus <= 1 or modulus % 2 == 0:
        raise ValueError(modulus)
    inv2k = pow(pow(2, slab.width, modulus), -1, modulus)
    return CollatzAffineResidue(
        modulus,
        pow(3, slab.ones, modulus) * inv2k,
        slab.offset * inv2k,
    )


def accelerated_odd_target_mod3_from_valuation(valuation: int) -> int:
    """Residue of ``(3*n+1)/2**valuation`` mod 3 for every odd source ``n``.

    The source disappears because ``3*n+1 == 1 (mod 3)``.  Thus the tropical
    valuation symbol already determines the whole mod-3 theorem interface; no
    parallel residue state is needed.
    """
    valuation = int(valuation)
    if valuation <= 0:
        raise ValueError(valuation)
    return pow(pow(2, valuation, 3), -1, 3)


__all__ = [
    "CollatzAffineResidue",
    "CollatzValuationProjectionBlock",
    "CollatzValuationStep",
    "Mul3CarryFn",
    "accelerated_odd_collatz",
    "accelerated_odd_target_mod3_from_valuation",
    "collatz_slab_mod_odd",
    "collatz_valuation_itinerary",
    "digits_lsd",
    "mul3_carry_monoid",
    "mul3_digit_carry_fn",
    "v2",
    "valuation_itinerary_slab",
    "valuation_projection_from_runs",
]
