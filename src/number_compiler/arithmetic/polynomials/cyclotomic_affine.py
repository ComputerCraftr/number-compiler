"""Canonical affine cocycle on one cyclotomic digit module."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import AffineCocycle, binary_power
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock


@dataclass(frozen=True, slots=True)
class CyclotomicAffineMorphism:
    """Canonical affine execution IR on one cyclotomic digit module.

    The map is ``x -> multiplier*x + addend`` in the fixed quotient ring.
    It is deliberately length-agnostic: sequence families keep physical width
    as a separate scalar and supply the result length when applying the map.
    This one object replaces family-specific composition loops for shifts,
    reverse-add ``2/(1+z)`` transport, Collatz radix-affine maps and the
    normalization factor ``base-z``.
    """

    order: int
    modulus: int
    power: int
    factor: tuple[int, ...] | None
    multiplier: tuple[int, ...]
    addend: tuple[int, ...]
    compositions: int = 0

    def __post_init__(self) -> None:
        ring = CyclotomicRing(self.order, self.modulus, self.power, self.factor)
        if len(self.multiplier) != ring.degree or len(self.addend) != ring.degree:
            raise ValueError((len(self.multiplier), len(self.addend), ring.degree))
        object.__setattr__(
            self, "multiplier", tuple(int(v) % self.modulus for v in self.multiplier)
        )
        object.__setattr__(
            self, "addend", tuple(int(v) % self.modulus for v in self.addend)
        )
        if int(self.compositions) < 0:
            raise ValueError(self.compositions)
        object.__setattr__(self, "compositions", int(self.compositions))

    @property
    def ring(self) -> CyclotomicRing:
        return CyclotomicRing(self.order, self.modulus, self.power, self.factor)

    @property
    def module_key(self) -> tuple[object, ...]:
        return self.ring.module_key

    @classmethod
    def identity_for(cls, template: CyclotomicDigitBlock) -> CyclotomicAffineMorphism:
        return cls(
            template.order,
            template.modulus,
            template.power,
            template.factor,
            template.ring.one,
            template.ring.zero,
            0,
        )

    @classmethod
    def from_residues(
        cls,
        template: CyclotomicDigitBlock,
        multiplier: Sequence[int],
        addend: Sequence[int],
    ) -> CyclotomicAffineMorphism:
        if len(multiplier) != template.degree or len(addend) != template.degree:
            raise ValueError((len(multiplier), len(addend), template.degree))
        return cls(
            template.order,
            template.modulus,
            template.power,
            template.factor,
            tuple(multiplier),
            tuple(addend),
            0,
        )

    @classmethod
    def from_polynomials(
        cls,
        template: CyclotomicDigitBlock,
        multiplier: Sequence[int],
        addend: Sequence[int],
    ) -> CyclotomicAffineMorphism:
        m = template.ring.reduce(multiplier)
        a = template.ring.reduce(addend)
        return cls.from_residues(template, m, a)

    @classmethod
    def scale(
        cls, template: CyclotomicDigitBlock, scalar: int
    ) -> CyclotomicAffineMorphism:
        return cls.from_polynomials(template, (int(scalar),), (0,))

    def _template(self) -> CyclotomicDigitBlock:
        return CyclotomicDigitBlock.identity(
            self.order,
            self.modulus,
            power=self.power,
            factor=self.factor,
        )

    @property
    def cocycle(self) -> AffineCocycle[tuple[int, ...]]:
        return AffineCocycle(self.multiplier, self.addend)

    def _then_raw(self, other: CyclotomicAffineMorphism) -> CyclotomicAffineMorphism:
        if self.module_key != other.module_key:
            raise ValueError((self.module_key, other.module_key))
        ring = self.ring
        cocycle = self.cocycle.then(
            other.cocycle,
            multiply=ring.multiply,
            add=ring.add,
        )
        return CyclotomicAffineMorphism(
            self.order,
            self.modulus,
            self.power,
            self.factor,
            cocycle.multiplier,
            cocycle.addend,
            0,
        )

    def then(self, other: CyclotomicAffineMorphism) -> CyclotomicAffineMorphism:
        out = self._then_raw(other)
        return CyclotomicAffineMorphism(
            out.order,
            out.modulus,
            out.power,
            out.factor,
            out.multiplier,
            out.addend,
            self.compositions + other.compositions + 1,
        )

    def power_map(self, exponent: int) -> CyclotomicAffineMorphism:
        base = CyclotomicAffineMorphism(
            self.order,
            self.modulus,
            self.power,
            self.factor,
            self.multiplier,
            self.addend,
            0,
        )
        powered = binary_power(
            base,
            exponent,
            identity=CyclotomicAffineMorphism.identity_for(self._template()),
            compose=CyclotomicAffineMorphism._then_raw,
        )
        result = powered.value
        return CyclotomicAffineMorphism(
            result.order,
            result.modulus,
            result.power,
            result.factor,
            result.multiplier,
            result.addend,
            powered.compositions,
        )

    @property
    def is_identity(self) -> bool:
        return self.multiplier == self.ring.one and self.addend == self.ring.zero

    def apply(
        self,
        block: CyclotomicDigitBlock,
        *,
        result_length: int | None = None,
    ) -> CyclotomicDigitBlock:
        if block.module_key != self.module_key:
            raise ValueError((block.module_key, self.module_key))
        target_length = block.length if result_length is None else int(result_length)
        if self.is_identity:
            if target_length == block.length:
                return block
            if target_length < 0:
                raise ValueError(target_length)
            return CyclotomicDigitBlock(
                block.order,
                block.modulus,
                target_length,
                block.residue,
                block.compositions,
                block.power,
                block.factor,
            )
        ring = self.ring
        product = ring.multiply(block.residue, self.multiplier)
        residue = ring.add(product, self.addend)
        return CyclotomicDigitBlock(
            block.order,
            block.modulus,
            target_length,
            residue,
            block.compositions + self.compositions + 1,
            block.power,
            block.factor,
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "cyclotomic-affine-morphism",
            self.module_key,
            self.multiplier,
            self.addend,
        )


__all__ = ["CyclotomicAffineMorphism"]
