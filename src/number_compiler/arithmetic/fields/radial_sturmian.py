"""Source-neutral, exact Archimedean rotation port for 3**H / 2**D.

The phase is {H*log_2(3)}; the integer dyadic shift D changes the
homogeneous order but not the phase.  A finite prefix is an *observation*
of the homogeneous multiplier, NOT of an affine endpoint. It never supplies
source-cylinder admission or a new Hashlife action identity.

Leading prefixes are certified with rational log intervals and an ordered
threshold search. Large exponents are never turned into 3**H: exact power
fallback is restricted to cases where the *requested prefix itself* is at
least as wide as the full integer 3**H. Work/precision limits fail closed.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.mechanical_readout import (
    MechanicalBlock,
    interval,
)
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys


@dataclass(frozen=True, slots=True)
class RadialSturmianPacket:
    """Certified leading bits of the homogeneous factor (not its endpoint)."""

    growths: int
    halvings: int
    binary_order: int
    prefix_width: int
    prefix_value: int
    precision_bits: int
    scope: str = "homogeneous multiplier; affine endpoint is not inferred"

    def __post_init__(self) -> None:
        HomogeneousGrowthScale(self.growths, self.halvings)
        require_integer(self.binary_order, "binary order")
        require_integer(self.prefix_width, "radial prefix width", 1)
        require_integer(self.prefix_value, "radial prefix", 0)
        require_integer(self.precision_bits, "radial certified precision", 0)
        if self.prefix_value.bit_length() != self.prefix_width:
            raise ValueError("radial prefix must contain exactly the requested bits")

    @property
    def prefix_binary(self) -> str:
        return format(self.prefix_value, f"0{self.prefix_width}b")


@dataclass(frozen=True, slots=True)
class RadialSturmianClock:
    """Powered additive exponent port for an already authorized source action.

    ``then`` and ``power`` do not enumerate temporal events. Source validation
    is deliberately owned by the Collatz or Mahler action, not by this clock.
    """

    scale: HomogeneousGrowthScale = field(
        default_factory=HomogeneousGrowthScale.identity
    )

    def __post_init__(self) -> None:
        if type(self.scale) is not HomogeneousGrowthScale:
            raise TypeError("radial clock requires the exact exponent descriptor")

    def then(self, after: RadialSturmianClock) -> RadialSturmianClock:
        if type(after) is not RadialSturmianClock:
            raise TypeError("radial clock requires another radial clock")
        return RadialSturmianClock(self.scale.then(after.scale))

    def power(self, count: int) -> RadialSturmianClock:
        return RadialSturmianClock(self.scale.power(count))

    def width_increment(
        self, evaluator: GrowthArithmeticEvaluator, start: int, count: int
    ) -> int:
        """Telescoped mechanical width word on ``[start, start+count)``.

        For ``scale=(3/2)``, this is the number of Sturmian 1s; for ``3`` it
        includes one unconditional bit per step. Neither query replays bits.
        """
        return interval(
            evaluator, MechanicalBlock(self.scale, start, count), 0, count, radix=2
        )

    def next_tripling_width_bit(self, evaluator: GrowthArithmeticEvaluator) -> int:
        """Exact Sturmian w_H; 3**(H+1) grows by 1+w_H binary places.

        The next second leading bit of 3**(H+1) is ``1 - w_H``.
        For fixed dyadic-shifted powers (3/2)**H, w_H itself is the
        next homogeneous binary-order increment. It is not an endpoint bit.
        """
        step = RadialSturmianClock(HomogeneousGrowthScale(1, 1))
        bit = step.width_increment(evaluator, self.scale.growths, 1)
        if bit not in (0, 1):
            raise ArithmeticError("irrational rotation width jump is not Boolean")
        return bit

    def leading_binary(
        self, evaluator: GrowthArithmeticEvaluator, width: int = 8
    ) -> RadialSturmianPacket:
        """Certify H_m(H)=floor(2**(m-1+{H log_2(3)}))."""
        if type(evaluator) is not GrowthArithmeticEvaluator:
            raise TypeError("radial readout requires a growth evaluator")
        require_integer(width, "radial prefix width", 1)
        if width > evaluator.max_precision_bits:
            evaluator.ledger.bump(_shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS)
            raise BlockContextBudgetExceeded("radial prefix exceeds precision budget")
        evaluator._ensure_open()
        if self.scale.is_identity and width <= 64:
            # The identity is a fixed machine-word readout, like radix_order's
            # identity shortcut. It needs no logarithm cache or scratch arena;
            # zero-event publishers can already occupy their entire node budget.
            evaluator.ledger.bump(_fields_keys.GROWTH_RADIAL_IDENTITY_SHORTCUTS)
            return RadialSturmianPacket(0, 0, 0, width, 1 << (width - 1), 0)
        with evaluator._charge_work(max(1, width), 0, width, storage_bits=8 * width):
            return self._leading_binary_admitted(evaluator, width)

    def _leading_binary_admitted(
        self, evaluator: GrowthArithmeticEvaluator, width: int
    ) -> RadialSturmianPacket:
        scale = self.scale
        order = evaluator.radix_order(scale, 2)
        # Normalization cancels every 2**D. The special case H=0 is exact.
        if scale.growths == 0:
            return RadialSturmianPacket(
                0, scale.halvings, order, width, 1 << (width - 1), 0
            )
        # An exact construction is justified only if its *complete* integer
        # fits the requested readout width; it cannot hide exponential work.
        full_width = order + scale.halvings + 1
        if full_width <= width:
            with evaluator._charge_work(
                max(1, width * scale.growths.bit_length()),
                0,
                width,
                storage_bits=4 * width,
            ):
                numerator = 3**scale.growths
                prefix = numerator << (width - numerator.bit_length())
            return RadialSturmianPacket(
                scale.growths, scale.halvings, order, width, prefix, 0
            )

        # Phase accuracy depends on the exponent bit length; the threshold
        # log_2(j/2**(m-1)) depends only on the requested m-bit prefix.
        # Refine their intervals *independently*. Sharing a single precision
        # forces every small threshold logarithm to exponent-scale precision,
        # making large temporal powers needlessly expensive.
        phase_precision = min(32, evaluator.max_precision_bits)
        threshold_precision = min(32, evaluator.max_precision_bits)
        phase_low, phase_high = evaluator.order_bounds(
            scale, 2, precision_bits=phase_precision
        )
        phase_low -= order
        phase_high -= order
        lo = 1 << (width - 1)
        hi = 1 << width
        highest_used = phase_precision
        denominator = 1 << (width - 1)
        while hi - lo > 1:
            middle = (lo + hi) // 2
            threshold_low, threshold_high = evaluator.binary_log_ratio_bounds(
                middle, denominator, precision_bits=threshold_precision
            )
            while True:
                highest_used = max(phase_precision, threshold_precision)
                if phase_low >= threshold_high:
                    lo = middle
                    break
                if phase_high < threshold_low:
                    hi = middle
                    break
                # Choose the uncertainty that dominates the comparison;
                # re-evaluate only that interval. A budget refusal remains
                # explicit rather than silently selecting either bit.
                phase_gap = phase_high - phase_low
                threshold_gap = threshold_high - threshold_low
                if (
                    phase_gap >= threshold_gap
                    or threshold_precision == evaluator.max_precision_bits
                ) and phase_precision < evaluator.max_precision_bits:
                    phase_precision = min(
                        phase_precision * 2, evaluator.max_precision_bits
                    )
                    phase_low, phase_high = evaluator.order_bounds(
                        scale, 2, precision_bits=phase_precision
                    )
                    phase_low -= order
                    phase_high -= order
                elif threshold_precision < evaluator.max_precision_bits:
                    threshold_precision = min(
                        threshold_precision * 2, evaluator.max_precision_bits
                    )
                    threshold_low, threshold_high = evaluator.binary_log_ratio_bounds(
                        middle, denominator, precision_bits=threshold_precision
                    )
                else:
                    evaluator.ledger.bump(
                        _shared_keys.GROWTH_ARITHMETIC_BUDGET_REFUSALS
                    )
                    raise BlockContextBudgetExceeded(
                        "radial leading-bit threshold unresolved at precision budget"
                    )
        return RadialSturmianPacket(
            scale.growths, scale.halvings, order, width, lo, highest_used
        )


__all__ = ["RadialSturmianClock", "RadialSturmianPacket"]
