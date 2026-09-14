"""Radial-mode quotients for affine sequence transports.

The sequence families in this repository often have a large predictable
multiplicative mode and a much smaller innovation term.  Retaining the large
coefficient itself is duplicate state: its valuation/exponent is enough, while
future semantics depend on the additive forcing cocycle and a bounded unit or
cyclotomic phase.

This module owns the reverse-add instance of that pattern.  Collatz already
uses the generic :mod:`number_compiler.arithmetic.fields.adic_morphism` implementation; its exact
``3**H / 2**K`` scale is exposed through ``PadicAffineMorphism.radial_quotient``.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.polynomials.cyclotomic_affine import (
    CyclotomicAffineMorphism,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    PowerTwoCyclotomicRadialQuotient,
    power_two_cyclotomic_radial_quotient,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock


@dataclass(frozen=True, slots=True)
class ReverseAddCyclotomicInnovationBlock:
    """Exact affine reverse-add block in one power-of-two cyclotomic factor.

    For a block containing ``q`` no-growth and ``r`` growth transitions,

    ``S_out = 2**q (1+z)**r S_in + B``.

    Only ``B`` is retained as the nonlinear innovation.  The multiplier is
    reconstructed from the two scalar counts and can be split into its radial
    valuation/unit phase with :attr:`radial`.  This avoids retaining a carry
    history or a second full pair field.
    """

    order: int
    bits: int
    steps: int
    growth: int
    innovation: tuple[int, ...]
    compositions: int = 0

    def __post_init__(self) -> None:
        order, bits = int(self.order), int(self.bits)
        steps, growth = int(self.steps), int(self.growth)
        if order < 2 or order & (order - 1) or bits <= 0:
            raise ValueError((order, bits))
        if steps < 0 or not 0 <= growth <= steps or int(self.compositions) < 0:
            raise ValueError(self)
        template = CyclotomicDigitBlock.identity(order, 1 << bits)
        if len(self.innovation) != template.degree:
            raise ValueError((len(self.innovation), template.degree))
        modulus = 1 << bits
        object.__setattr__(self, "order", order)
        object.__setattr__(self, "bits", bits)
        object.__setattr__(self, "steps", steps)
        object.__setattr__(self, "growth", growth)
        object.__setattr__(
            self, "innovation", tuple(int(v) % modulus for v in self.innovation)
        )
        object.__setattr__(self, "compositions", int(self.compositions))

    @property
    def modulus(self) -> int:
        return 1 << self.bits

    @property
    def classes(self) -> int:
        return self.order // 2

    @property
    def no_growth(self) -> int:
        return self.steps - self.growth

    def _template(self) -> CyclotomicDigitBlock:
        return CyclotomicDigitBlock.identity(self.order, self.modulus)

    @classmethod
    def identity(cls, *, order: int, bits: int) -> ReverseAddCyclotomicInnovationBlock:
        template = CyclotomicDigitBlock.identity(int(order), 1 << int(bits))
        return cls(int(order), int(bits), 0, 0, (0,) * template.degree, 0)

    @classmethod
    def atom(
        cls,
        event: Sequence[int],
        growth: int,
        *,
        order: int,
        bits: int,
    ) -> ReverseAddCyclotomicInnovationBlock:
        g = int(growth)
        if g not in (0, 1):
            raise ValueError(g)
        block = CyclotomicDigitBlock.from_coefficients(
            tuple(map(int, event)),
            order=int(order),
            modulus=1 << int(bits),
        )
        return cls(int(order), int(bits), 1, g, block.residue, 0)

    @classmethod
    def from_events(
        cls,
        events: Sequence[Sequence[int]],
        growths: Sequence[int],
        *,
        order: int,
        bits: int,
    ) -> ReverseAddCyclotomicInnovationBlock:
        rows = tuple(tuple(map(int, row)) for row in events)
        gs = tuple(map(int, growths))
        if len(rows) != len(gs):
            raise ValueError((len(rows), len(gs)))
        out = cls.identity(order=int(order), bits=int(bits))
        for event, growth in zip(rows, gs, strict=True):
            out = out.then(cls.atom(event, growth, order=int(order), bits=int(bits)))
        return out

    @property
    def radial(self) -> PowerTwoCyclotomicRadialQuotient:
        return power_two_cyclotomic_radial_quotient(
            self.classes,
            self.no_growth,
            self.growth,
            bits=self.bits,
        )

    @property
    def source_annihilated(self) -> bool:
        return self.radial.annihilated

    def linear_morphism(self) -> CyclotomicAffineMorphism:
        template = self._template()
        multiplier = self.radial.multiplier_residue()
        return CyclotomicAffineMorphism.from_residues(
            template,
            multiplier,
            (0,) * template.degree,
        )

    def affine_morphism(self) -> CyclotomicAffineMorphism:
        template = self._template()
        return CyclotomicAffineMorphism.from_residues(
            template,
            self.radial.multiplier_residue(),
            self.innovation,
        )

    def then(
        self, other: ReverseAddCyclotomicInnovationBlock
    ) -> ReverseAddCyclotomicInnovationBlock:
        if (self.order, self.bits) != (other.order, other.bits):
            raise ValueError(((self.order, self.bits), (other.order, other.bits)))
        composed = self.affine_morphism().then(other.affine_morphism())
        total = ReverseAddCyclotomicInnovationBlock(
            self.order,
            self.bits,
            self.steps + other.steps,
            self.growth + other.growth,
            composed.addend,
            self.compositions + other.compositions + 1,
        )
        if composed.multiplier != total.radial.multiplier_residue():
            raise AssertionError("radial counts disagree with affine composition")
        return total

    def power_block(self, exponent: int) -> ReverseAddCyclotomicInnovationBlock:
        identity = ReverseAddCyclotomicInnovationBlock.identity(
            order=self.order, bits=self.bits
        )
        base = ReverseAddCyclotomicInnovationBlock(
            self.order,
            self.bits,
            self.steps,
            self.growth,
            self.innovation,
            0,
        )
        powered = binary_power(
            base,
            exponent,
            identity=identity,
            compose=ReverseAddCyclotomicInnovationBlock.then,
        )
        result = powered.value
        return ReverseAddCyclotomicInnovationBlock(
            result.order,
            result.bits,
            result.steps,
            result.growth,
            result.innovation,
            powered.compositions,
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # The large radial multiplier is represented only through its exact
        # quotient key.  Construction provenance and carry/event histories are
        # deliberately absent.
        return (
            "reverse-add-cyclotomic-innovation",
            self.order,
            self.bits,
            self.radial.canonical_key,
            self.innovation,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.order)
            + bit_width(self.bits)
            + bit_width(self.steps)
            + bit_width(self.growth)
            + sum(bit_width(v) for v in self.innovation)
        )


__all__ = ["ReverseAddCyclotomicInnovationBlock"]
