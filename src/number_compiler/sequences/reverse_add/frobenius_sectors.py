"""Exact bounded affine products derived from reverse carry-domain summaries.

Carry transfers determine growth and forcing; callers need not supply an event
itinerary.  The authenticated tile observation derives a powered product from
its endpoint-interface summaries.  Explicit event constructors remain useful
for independent algebra checks.  Every product contains bounded cyclotomic
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
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    ReverseFrobeniusPlan,
)
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_radial_quotient,
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
    def from_annihilated_source(
        cls,
        initial_width: int,
        final_input: ReverseCarrySectorTransfer,
        plan: ReverseFrobeniusPlan,
    ) -> ReverseFrobeniusSectorProduct:
        """Observe innovation when the certified source multiplier is zero.

        Only the original extent remains relevant to the growth cocycle.  No
        original coefficients are requested or synthesized.  As with endpoint
        observation, the caller authenticates the symmetric whole-field binding;
        this constructor does not authorize an arbitrary interval as a field.
        """
        if type(initial_width) is not int:
            raise TypeError("source extent requires an exact integer")
        if type(plan) is not ReverseFrobeniusPlan:
            raise TypeError("source annihilation requires a Frobenius plan")
        if type(final_input) is not ReverseCarrySectorTransfer:
            raise TypeError("final sectors require a canonical carry transfer")
        plan.__post_init__()
        final_input.__post_init__()
        if (
            initial_width < 1
            or final_input.base != 10
            or not final_input.active_width
            or (plan.maximum_classes, plan.bits) != (8, 5)
            or not plan.all_source_sectors_annihilated
        ):
            raise ValueError(
                "source annihilation is not proved for this sector profile"
            )
        observation = final_input.forcing(0)
        growth = final_input.active_width + observation.growth - initial_width
        if not 0 <= growth <= plan.steps:
            raise ValueError("endpoint widths disagree with temporal growth")
        sectors = tuple(
            ReverseAddCyclotomicInnovationBlock(
                2 * sector.classes,
                5,
                plan.steps,
                growth,
                sector.output,
                0,
            )
            for sector in observation.sectors
        )
        return cls(8, 5, plan.steps, growth, sectors)

    @classmethod
    def from_endpoint_sectors(
        cls,
        initial: ReverseCarrySectorTransfer,
        final_input: ReverseCarrySectorTransfer,
        steps: int,
    ) -> ReverseFrobeniusSectorProduct:
        """Recover a block affine product from two bounded sector observations.

        ``final_input`` is the complete symmetric pair field immediately before
        the last of ``steps`` transitions.  Its carry law derives the final
        growth and output residue.  The caller must authenticate whole-field
        mirror symmetry; arbitrary interval summaries are not admissible.
        """
        if (
            type(initial) is not ReverseCarrySectorTransfer
            or type(final_input) is not ReverseCarrySectorTransfer
        ):
            raise TypeError("endpoint sectors require canonical carry transfers")
        initial.__post_init__()
        final_input.__post_init__()
        if type(steps) is not int or steps < 1:
            raise ValueError("endpoint sector steps require a positive exact integer")
        if (
            initial.base != 10
            or final_input.base != 10
            or not initial.active_width
            or not final_input.active_width
        ):
            raise ValueError("endpoint sectors require active decimal fields")
        observation = final_input.forcing(0)
        total_growth = (
            final_input.active_width + observation.growth - initial.active_width
        )
        if not 0 <= total_growth <= steps:
            raise ValueError("endpoint widths disagree with temporal growth")
        no_growth = steps - total_growth
        sectors: list[ReverseAddCyclotomicInnovationBlock] = []
        for source, output in zip(initial.sectors, observation.sectors, strict=True):
            if source.classes != output.classes:
                raise ValueError("endpoint sectors have another fixed profile")
            multiplier = power_two_cyclotomic_radial_quotient(
                source.classes,
                no_growth,
                total_growth,
                bits=5,
            ).multiplier_residue()
            ring = CyclotomicRing(2 * source.classes, 32)
            innovation = ring.subtract(
                output.output,
                ring.multiply(multiplier, source.symbols),
            )
            sectors.append(
                ReverseAddCyclotomicInnovationBlock(
                    2 * source.classes,
                    5,
                    steps,
                    total_growth,
                    innovation,
                    0,
                )
            )
        return cls(8, 5, steps, total_growth, tuple(sectors))

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
