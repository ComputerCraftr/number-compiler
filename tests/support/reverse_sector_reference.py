"""Endpoint-based sector identities used only as independent test references.

These formulas require an executed final input. They are not production
constructors and must never be imported by the source cylinder scheduler.
"""

from __future__ import annotations

from devtools.experiments.reverse_add.frobenius_sectors import (
    ReverseFrobeniusSectorProduct,
)
from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
)
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_radial_quotient,
)
from number_compiler.arithmetic.polynomials.frobenius_sector import ReverseFrobeniusPlan


def from_annihilated_source(
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
        raise ValueError("source annihilation is not proved for this sector profile")
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
    return ReverseFrobeniusSectorProduct(8, 5, plan.steps, growth, sectors)


def from_endpoint_sectors(
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
    total_growth = final_input.active_width + observation.growth - initial.active_width
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
    return ReverseFrobeniusSectorProduct(8, 5, steps, total_growth, tuple(sectors))
