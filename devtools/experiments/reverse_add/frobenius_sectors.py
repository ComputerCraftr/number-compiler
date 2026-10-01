"""Research-only affine products from reverse carry-domain summaries.

These products are bounded reference observations, not installed successor
authority or a source-image construction path.

Carry transfers determine growth and forcing; callers need not supply an event
itinerary for a primitive step. Powered source extraction must be constructed
by the source cylinder adapter; endpoint recovery is not a production path.
Explicit event constructors remain useful for independent algebra checks.  Every product contains bounded cyclotomic
residues, never an output field or trajectory record.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
)
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    ReverseFrobeniusPlan,
)


def _canonical_block(
    block: ReverseAddCyclotomicInnovationBlock,
) -> ReverseAddCyclotomicInnovationBlock:
    return ReverseAddCyclotomicInnovationBlock(
        block.order,
        block.bits,
        block.steps,
        block.growth,
        block.innovation,
        0,
    )


@dataclass(frozen=True, slots=True)
class ReverseFrobeniusSectorProduct:
    """Fixed-arity exact affine quotient for one observed temporal block."""

    maximum_classes: int
    bits: int
    steps: int
    growth: int
    sectors: tuple[ReverseAddCyclotomicInnovationBlock, ...]

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.maximum_classes,
                self.bits,
                self.steps,
                self.growth,
            )
        ):
            raise TypeError("reverse sector products require exact integers")
        plan = ReverseFrobeniusPlan.for_steps(
            maximum_classes=self.maximum_classes,
            bits=self.bits,
            steps=self.steps,
        )
        if not 0 <= self.growth <= self.steps or type(self.sectors) is not tuple:
            raise ValueError("invalid observed reverse branch counts")
        expected_orders = tuple(2 * sector.classes for sector in plan.sectors)
        if len(self.sectors) != len(expected_orders):
            raise ValueError("reverse sector product has another arity")
        for block, order in zip(self.sectors, expected_orders, strict=True):
            if type(block) is not ReverseAddCyclotomicInnovationBlock:
                raise TypeError("reverse sector product has another component sort")
            if (
                any(
                    type(value) is not int
                    for value in (
                        block.order,
                        block.bits,
                        block.steps,
                        block.growth,
                        block.compositions,
                    )
                )
                or type(block.innovation) is not tuple
                or any(type(value) is not int for value in block.innovation)
            ):
                raise TypeError("reverse sector component contains a numeric alias")
            if (
                block.order != order
                or block.bits != self.bits
                or block.steps != self.steps
                or block.growth != self.growth
                or block.compositions != 0
                or len(block.innovation) != order // 2
                or any(not 0 <= value < 1 << self.bits for value in block.innovation)
            ):
                raise ValueError("reverse sector component is not canonical")

    @classmethod
    def identity(
        cls,
        *,
        maximum_classes: int,
        bits: int,
    ) -> ReverseFrobeniusSectorProduct:
        plan = ReverseFrobeniusPlan.identity(
            maximum_classes=maximum_classes,
            bits=bits,
        )
        sectors = tuple(
            ReverseAddCyclotomicInnovationBlock.identity(
                order=2 * sector.classes,
                bits=bits,
            )
            for sector in plan.sectors
        )
        return cls(maximum_classes, bits, 0, 0, sectors)

    @classmethod
    def atom(
        cls,
        event: Sequence[int],
        growth: int,
        *,
        maximum_classes: int,
        bits: int,
    ) -> ReverseFrobeniusSectorProduct:
        if type(growth) is not int:
            raise TypeError("reverse growth observation requires an exact integer")
        if growth not in (0, 1):
            raise ValueError("reverse growth observation must be Boolean")
        plan = ReverseFrobeniusPlan.for_steps(
            maximum_classes=maximum_classes,
            bits=bits,
            steps=1,
        )
        if len(event) > maximum_classes:
            raise ValueError("reverse forcing event exceeds the bounded local stencil")
        coefficients = tuple(event)
        if any(type(value) is not int for value in coefficients):
            raise TypeError("reverse forcing coefficients require exact integers")
        if any(not -(1 << 63) <= value < 1 << 63 for value in coefficients):
            raise ValueError("reverse forcing coefficient exceeds one signed limb")
        sectors = tuple(
            ReverseAddCyclotomicInnovationBlock.atom(
                coefficients,
                growth,
                order=2 * sector.classes,
                bits=bits,
            )
            for sector in plan.sectors
        )
        return cls(maximum_classes, bits, 1, growth, sectors)

    @classmethod
    def from_carry_transfer(
        cls,
        summary: ReverseCarrySectorTransfer,
    ) -> ReverseFrobeniusSectorProduct:
        """Build one observed step from the closed decimal carry-domain product.

        ``summary`` must describe the complete contiguous symmetric pair field.
        Growth and innovation are derived by its normalization law; callers do
        not supply an event row or branch bit.
        """
        if type(summary) is not ReverseCarrySectorTransfer:
            raise TypeError("reverse sector product requires a carry transfer")
        summary.__post_init__()
        if summary.base != 10 or not summary.active_width:
            raise ValueError("reverse sector product requires an active decimal field")
        observation = summary.forcing(0)
        sectors = tuple(
            ReverseAddCyclotomicInnovationBlock(
                2 * sector.classes,
                5,
                1,
                observation.growth,
                sector.full,
                0,
            )
            for sector in observation.sectors
        )
        return cls(8, 5, 1, observation.growth, sectors)

    @classmethod
    def from_completed_causal_predecessor(
        cls,
        initial: ReverseCarrySectorTransfer | None,
        predecessor: ReverseCarrySectorTransfer,
        *,
        initial_width: int,
        steps: int,
        plan: ReverseFrobeniusPlan,
    ) -> ReverseFrobeniusSectorProduct:
        """Observe a powered affine product from its final primitive input.

        The completed causal interface exposes the pair-sector transfer for
        the input to the final primitive transition.  Its forcing gives the
        final output sectors directly.  When the certified source bound kills
        every initial sector, ``initial`` may be omitted and no initial source
        sector compilation is needed.

        This is a bounded observation of an existing tile execution.  It does
        not construct a successor source or authorize a source cylinder.
        """
        if type(predecessor) is not ReverseCarrySectorTransfer:
            raise TypeError("powered sector observation requires a causal predecessor")
        predecessor.__post_init__()
        if type(initial_width) is not int or initial_width < 1:
            raise ValueError("powered sector observation requires an initial width")
        if type(steps) is not int or steps < 1:
            raise ValueError("powered sector observation requires positive steps")
        if type(plan) is not ReverseFrobeniusPlan:
            raise TypeError("powered sector observation requires a source-bound plan")
        plan.__post_init__()
        if (
            plan.maximum_classes != 8
            or plan.bits != 5
            or plan.steps != steps
            or plan.growth_certificate is not DECIMAL_REVERSE_GROWTH_CERTIFICATE
            or predecessor.base != 10
            or predecessor.active_width < 1
        ):
            raise ValueError("powered sector observation differs from decimal profile")
        if initial is None:
            if not plan.all_source_sectors_annihilated:
                raise ValueError("powered source sectors are not proved annihilated")
        else:
            if type(initial) is not ReverseCarrySectorTransfer:
                raise TypeError("powered sector initial source has another sort")
            initial.__post_init__()
            if (
                initial.base != predecessor.base
                or initial.width != predecessor.width
                or initial.active_width != initial_width
            ):
                raise ValueError("powered sector source geometry changed")

        observed = predecessor.forcing(0)
        final_width = predecessor.active_width + observed.growth
        growth = final_width - initial_width
        if not 0 <= growth <= steps:
            raise ValueError("powered sector widths disagree with temporal growth")
        sectors: list[ReverseAddCyclotomicInnovationBlock] = []
        for index, output in enumerate(observed.sectors):
            classes = 1 << index
            if output.classes != classes:
                raise ValueError(
                    "powered sector predecessor has another sector profile"
                )
            radial_block = ReverseAddCyclotomicInnovationBlock(
                2 * classes,
                5,
                steps,
                growth,
                (0,) * classes,
                0,
            )
            ring = CyclotomicRing(2 * classes, 32)
            multiplier = radial_block.radial.multiplier_residue()
            if initial is None:
                innovation = output.output
                if not radial_block.source_annihilated:
                    raise ValueError(
                        "observed powered source sector survived its bound"
                    )
            else:
                source = initial.sectors[index]
                innovation = ring.subtract(
                    output.output,
                    ring.multiply(multiplier, source.symbols),
                )
            sectors.append(
                ReverseAddCyclotomicInnovationBlock(
                    2 * classes,
                    5,
                    steps,
                    growth,
                    innovation,
                    0,
                )
            )
        return cls(8, 5, steps, growth, tuple(sectors))

    def then(
        self,
        after: ReverseFrobeniusSectorProduct,
    ) -> ReverseFrobeniusSectorProduct:
        if type(after) is not ReverseFrobeniusSectorProduct:
            raise TypeError("sector composition requires another exact product")
        if (self.maximum_classes, self.bits) != (
            after.maximum_classes,
            after.bits,
        ):
            raise ValueError("reverse sector products use different profiles")
        sectors = tuple(
            _canonical_block(before.then(next_block))
            for before, next_block in zip(self.sectors, after.sectors, strict=True)
        )
        return ReverseFrobeniusSectorProduct(
            self.maximum_classes,
            self.bits,
            self.steps + after.steps,
            self.growth + after.growth,
            sectors,
        )

    @property
    def source_annihilated_sectors(self) -> tuple[bool, ...]:
        return tuple(block.source_annihilated for block in self.sectors)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "reverse-frobenius-sector-product-v1",
            self.maximum_classes,
            self.bits,
            tuple(block.canonical_key for block in self.sectors),
        )


__all__ = ["ReverseFrobeniusSectorProduct"]
