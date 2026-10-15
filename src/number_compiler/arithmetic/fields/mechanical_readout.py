"""Compact interval and point reads of homogeneous radix-growth blocks."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)


@dataclass(frozen=True, slots=True)
class MechanicalBlock:
    """A compact interval of the mechanical word induced by one scale.

    A point at index ``i`` is the difference between consecutive radix orders
    of powers of ``scale``.  An interval query telescopes those endpoints, so
    it is independent of the interval length and never replays its symbols.
    """

    scale: HomogeneousGrowthScale
    start: int
    length: int

    def __post_init__(self) -> None:
        if type(self.scale) is not HomogeneousGrowthScale:
            raise TypeError("mechanical block requires a homogeneous growth scale")
        require_integer(self.start, "mechanical block start", 0)
        require_integer(self.length, "mechanical block length", 0)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "mechanical-growth-block",
            self.scale.canonical_key,
            self.start,
            self.length,
        )


@dataclass(frozen=True, slots=True)
class HomogeneousGrowthPacket:
    """Named demanded readout; its order is not an endpoint-width claim."""

    growths: int
    halvings: int
    radix: int
    homogeneous_radix_order: int

    def __post_init__(self) -> None:
        HomogeneousGrowthScale(self.growths, self.halvings)
        require_integer(self.radix, "radix", 2)
        require_integer(self.homogeneous_radix_order, "homogeneous radix order")

    @property
    def scale(self) -> HomogeneousGrowthScale:
        return HomogeneousGrowthScale(self.growths, self.halvings)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "homogeneous-growth-packet",
            self.growths,
            self.halvings,
            self.radix,
            self.homogeneous_radix_order,
        )


def homogeneous_growth_packet(
    scale: HomogeneousGrowthScale,
    ledger: ResourceLedger,
    radix: int = 10,
    *,
    evaluator: GrowthArithmeticEvaluator | None = None,
    max_precision_bits: int = 1_000_000,
    max_work_units: int = 1_000_000,
) -> HomogeneousGrowthPacket:
    """Compute one exact packet using a caller evaluator or a temporary one.

    Without ``evaluator``, each packet demand owns and closes a temporary
    evaluator, so memoized constants are not reused by later packet calls.
    With one, the caller's evaluator supplies both cache reuse and budgets.
    """
    if type(scale) is not HomogeneousGrowthScale:
        raise TypeError("growth packets require a homogeneous growth scale")
    if type(ledger) is not ResourceLedger:
        raise TypeError("growth packets require a ResourceLedger")
    require_integer(radix, "radix", 2)
    require_integer(max_precision_bits, "growth precision budget", 1)
    require_integer(max_work_units, "growth work budget", 0)
    if evaluator is not None:
        if (
            type(evaluator) is not GrowthArithmeticEvaluator
            or evaluator.ledger is not ledger
        ):
            raise ValueError("packet evaluator must belong to the supplied ledger")
        if evaluator.is_closed:
            raise RuntimeError("packet evaluator has been closed")
    if scale.is_identity:
        ledger.bump(_fields_keys.GROWTH_ARITHMETIC_OPERAND_BITS, 0)
        ledger.bump(_fields_keys.GROWTH_ARITHMETIC_WORK, 0)
        ledger.bump(_fields_keys.GROWTH_ARITHMETIC_PRECISION_BITS, 0)
        ledger.bump(_fields_keys.GROWTH_ORDER_IDENTITY_SHORTCUTS)
        return HomogeneousGrowthPacket(0, 0, radix, 0)
    if evaluator is not None:
        order = evaluator.radix_order(scale, radix)
        return HomogeneousGrowthPacket(
            scale.growths,
            scale.halvings,
            radix,
            order,
        )
    with GrowthArithmeticEvaluator(
        ledger,
        max_precision_bits=max_precision_bits,
        max_work_units=max_work_units,
    ) as temporary_evaluator:
        order = temporary_evaluator.radix_order(scale, radix)
    return HomogeneousGrowthPacket(
        scale.growths,
        scale.halvings,
        radix,
        order,
    )


def point(
    evaluator: GrowthArithmeticEvaluator,
    block: MechanicalBlock,
    index: int,
    *,
    radix: int = 10,
) -> int:
    """Read one admitted point without constructing the represented scale."""
    if type(evaluator) is not GrowthArithmeticEvaluator:
        raise TypeError("mechanical readout requires a growth arithmetic evaluator")
    if type(block) is not MechanicalBlock:
        raise TypeError("mechanical readout requires a compact mechanical block")
    require_integer(index, "mechanical point index", 0)
    if index >= block.length:
        raise IndexError(index)
    return interval(evaluator, block, index, index + 1, radix=radix)


def interval(
    evaluator: GrowthArithmeticEvaluator,
    block: MechanicalBlock,
    lower: int,
    upper: int,
    *,
    radix: int = 10,
) -> int:
    """Return the exact weighted count on block-relative ``[lower, upper)``."""
    if type(evaluator) is not GrowthArithmeticEvaluator:
        raise TypeError("mechanical readout requires a growth arithmetic evaluator")
    if type(block) is not MechanicalBlock:
        raise TypeError("mechanical readout requires a compact mechanical block")
    require_integer(lower, "mechanical interval lower bound", 0)
    require_integer(upper, "mechanical interval upper bound", 0)
    require_integer(radix, "radix", 2)
    if lower > upper or upper > block.length:
        raise ValueError("mechanical interval lies outside its admitted block")
    if lower == upper:
        return 0
    start = block.start + lower
    stop = block.start + upper
    return evaluator.radix_order(
        block.scale.power(stop), radix
    ) - evaluator.radix_order(block.scale.power(start), radix)


def select_weighted(
    evaluator: GrowthArithmeticEvaluator,
    block: MechanicalBlock,
    rank: int,
    *,
    radix: int = 10,
) -> int:
    """Select the point containing a signed weighted rank by interval bisection.

    The search uses O(log(block.length)) exact interval reads.  It does not
    expand or scan the represented mechanical word, including when the block
    length is a huge symbolic integer.
    """
    if type(evaluator) is not GrowthArithmeticEvaluator:
        raise TypeError("mechanical selection requires a growth arithmetic evaluator")
    if type(block) is not MechanicalBlock:
        raise TypeError("mechanical selection requires a compact mechanical block")
    require_integer(rank, "mechanical weighted rank", 1)
    total = interval(evaluator, block, 0, block.length, radix=radix)
    if total == 0:
        raise IndexError("mechanical block has no weighted points")
    direction = 1 if total > 0 else -1
    if rank > abs(total):
        raise IndexError(rank)

    lower_count, upper_count = 1, block.length
    while lower_count < upper_count:
        middle_count = (lower_count + upper_count) // 2
        covered = direction * interval(evaluator, block, 0, middle_count, radix=radix)
        if covered >= rank:
            upper_count = middle_count
        else:
            lower_count = middle_count + 1
    return lower_count - 1


__all__ = [
    "HomogeneousGrowthPacket",
    "MechanicalBlock",
    "homogeneous_growth_packet",
    "interval",
    "point",
    "select_weighted",
]
