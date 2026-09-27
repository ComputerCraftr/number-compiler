"""Exact chronological weights for admitted comma boundary returns.

These arithmetic actions do not decide which fork child survives.  A caller
must bind a selected child to independently checked branch evidence.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.fields.consumer_pullback import ExactRational
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.sequences.comma.boundary_quotient import (
    PERIOD,
    AffineWeight,
    BoundaryState,
    MacroTemplate,
)

Q = ExactRational
ONE = Q(1)


def _weight_from_rationals(scale: Q, offset: Q) -> AffineWeight:
    return AffineWeight(
        scale.numerator * offset.denominator,
        offset.numerator * scale.denominator,
        scale.denominator * offset.denominator,
    )


@dataclass(frozen=True, slots=True)
class WeightedBoundaryAction:
    """Q-to-Q' return with literal transition weight `(A*10**p+B)/D`."""

    start: BoundaryState
    end: BoundaryState
    exponent_delta: int
    weight: AffineWeight

    def __post_init__(self) -> None:
        if type(self.start) is not BoundaryState or type(self.end) is not BoundaryState:
            raise TypeError("weighted comma return needs exact boundary states")
        if type(self.exponent_delta) is not int or self.exponent_delta < 0:
            raise ValueError("weighted comma exponent transport must be nonnegative")
        if (
            self.start.exponent_residue + self.exponent_delta
        ) % PERIOD != self.end.exponent_residue:
            raise ValueError("weighted comma return has inconsistent exponent residue")
        if type(self.weight) is not AffineWeight:
            raise TypeError("weighted comma return needs an exact affine weight")
        weight = self.weight
        if weight.numerator_scale < 0:
            raise ValueError("weighted comma return has decreasing source weight")
        if weight.numerator_scale == 0:
            if (
                weight.numerator_offset < 0
                or weight.numerator_offset % weight.denominator
            ):
                raise ValueError("weighted comma return is not a natural literal count")
            if weight.numerator_offset == 0:
                if self.start != self.end or self.exponent_delta != 0:
                    raise ValueError("weighted comma return has no literal progress")
            elif self.start == self.end and self.exponent_delta == 0:
                raise ValueError("weighted comma return cannot revisit a fixed value")
            return
        least_exponent = self.start.exponent_residue
        if least_exponent < 5:
            least_exponent += PERIOD
        least_scale = int(pow(10, least_exponent))
        least_numerator = weight.numerator_scale * least_scale + weight.numerator_offset
        if least_numerator <= 0 or least_numerator % weight.denominator:
            raise ValueError("weighted comma return is not a natural literal count")
        if self.start == self.end and self.exponent_delta == 0:
            raise ValueError("weighted comma return cannot revisit a fixed value")
        if (
            weight.denominator > 1
            and (
                weight.numerator_scale
                * pow(10, least_exponent, weight.denominator)
                * (pow(10, PERIOD, weight.denominator) - 1)
            )
            % weight.denominator
        ):
            raise ValueError("weighted comma return is not integral on its residue ray")

    @classmethod
    def identity(cls, state: BoundaryState) -> WeightedBoundaryAction:
        return cls(state, state, 0, AffineWeight(0, 0, 1))

    @classmethod
    def from_selected_fork(
        cls, macro: MacroTemplate, selected_child: BoundaryState
    ) -> WeightedBoundaryAction:
        """Add the one fork-choice tick; this does not certify selection."""
        if type(macro) is not MacroTemplate or macro.outcome != "fork":
            raise ValueError("weighted boundary return requires a fork macro")
        if (
            type(selected_child) is not BoundaryState
            or selected_child not in macro.ordered_children
        ):
            raise ValueError("selected comma child is not an exact fork alternative")
        weight = macro.weight
        return cls(
            macro.source,
            selected_child,
            macro.exponent_delta,
            AffineWeight(
                weight.numerator_scale,
                weight.numerator_offset + weight.denominator,
                weight.denominator,
            ),
        )

    def then(
        self,
        after: WeightedBoundaryAction,
        *,
        charge: Callable[[int], None] | None = None,
        charge_bits: Callable[[int], None] | None = None,
    ) -> WeightedBoundaryAction:
        """Chronological composition through the shared skew action law."""
        if type(after) is not WeightedBoundaryAction or self.end != after.start:
            raise ValueError("weighted comma actions have different boundary bindings")
        if charge is not None:
            charge(1)
        if charge_bits is not None:
            charge_bits(
                self.exponent_delta.bit_length()
                + after.exponent_delta.bit_length()
                + self.weight.numerator_scale.bit_length()
                + after.weight.numerator_scale.bit_length()
                + self.weight.numerator_offset.bit_length()
                + after.weight.numerator_offset.bit_length()
                + self.weight.denominator.bit_length()
                + after.weight.denominator.bit_length()
            )
        # Constructor invariants make zero weight exactly the identity at its
        # bound state. Bindings and work admission are checked before reuse.
        if self.weight.numerator_scale == 0 and self.weight.numerator_offset == 0:
            return after
        if after.weight.numerator_scale == 0 and after.weight.numerator_offset == 0:
            return self
        left_scale = Q(self.weight.numerator_scale, self.weight.denominator)
        right_scale = Q(after.weight.numerator_scale, after.weight.denominator)
        # Only the offset projection is consumed: right.lower affects only
        # joined.lower, while left.lower matters only if right_scale is live.
        if right_scale.numerator:
            if charge_bits is not None:
                charge_bits(4 * self.exponent_delta + 1)
            left_lower = Q(pow(10, self.exponent_delta))
        else:
            left_lower = ONE
        left = SkewTransfer(ONE, left_scale, left_lower)
        right = SkewTransfer(ONE, right_scale, ONE)
        joined = left.then(right, multiply=lambda x, y: x * y, add=lambda x, y: x + y)
        constant = Q(self.weight.numerator_offset, self.weight.denominator) + Q(
            after.weight.numerator_offset, after.weight.denominator
        )
        return WeightedBoundaryAction(
            self.start,
            after.end,
            self.exponent_delta + after.exponent_delta,
            _weight_from_rationals(joined.offset, constant),
        )

    def repeat(self, count: int) -> RepeatedBoundaryReturn:
        if self.start != self.end:
            raise ValueError("comma repetition requires a complete Q-to-Q return")
        if type(count) is not int or count < 0:
            raise ValueError("comma repetition count must be nonnegative")
        if self.weight.numerator_scale < 0:
            raise ValueError("comma repeated weight needs nonnegative scale")
        return RepeatedBoundaryReturn(self, count)


def _capped_geometric(
    base: int,
    count: int,
    cap: int,
    charge: Callable[[int], None] | None,
    charge_bits: Callable[[int], None] | None,
) -> int:
    """Use shared binary squaring over the capped skew semiring."""

    def capped_product(left: int, right: int) -> int:
        if charge_bits is not None:
            charge_bits(left.bit_length() + right.bit_length())
        return min(cap, left * right)

    def capped_sum(left: int, right: int) -> int:
        if charge_bits is not None:
            charge_bits(left.bit_length() + right.bit_length())
        return min(cap, left + right)

    def compose(
        first: SkewTransfer[int], second: SkewTransfer[int]
    ) -> SkewTransfer[int]:
        if charge is not None:
            charge(1)
        return first.then(second, multiply=capped_product, add=capped_sum)

    powered = binary_power(
        SkewTransfer(1, 1, min(base, cap)),
        count,
        identity=SkewTransfer(1, 0, 1),
        compose=compose,
    )
    return powered.value.offset


@dataclass(frozen=True, slots=True)
class RepeatedBoundaryReturn:
    """Compact `(Q→Q)^count` with geometric literal-term weight."""

    base: WeightedBoundaryAction
    count: int

    def __post_init__(self) -> None:
        if (
            type(self.base) is not WeightedBoundaryAction
            or self.base.start != self.base.end
        ):
            raise ValueError("repeated comma return requires a complete Q-to-Q action")
        if type(self.count) is not int or self.count < 0:
            raise ValueError("repeated comma return count must be nonnegative")
        if self.base.weight.numerator_scale < 0:
            raise ValueError("repeated comma return needs nonnegative scale")

    @property
    def exponent_delta(self) -> int:
        return self.base.exponent_delta * self.count

    def split_at(
        self,
        exponent: int,
        transitions: int,
        *,
        charge: Callable[[int], None] | None = None,
        charge_bits: Callable[[int], None] | None = None,
    ) -> tuple[int, int]:
        """Find the largest completed return count and its literal remainder.

        The geometric prefix is capped at a threshold that still distinguishes
        every prefix whose actual weight can fit in ``transitions``.  One
        binary descent visits O(log count) summary blocks, with no fork replay.
        """
        if (
            type(exponent) is not int
            or exponent < 5
            or exponent % PERIOD != self.base.start.exponent_residue
        ):
            raise ValueError("repeated comma return has another source exponent")
        if type(transitions) is not int or transitions < 0:
            raise ValueError("comma literal offset must be nonnegative")
        if self.count == 0:
            if transitions:
                raise ValueError("comma literal offset exceeds repeated return")
            return 0, 0
        weight = self.base.weight
        if transitions == 0:
            if charge is not None:
                charge(1)
            # Every admitted nonidentity boundary return has strictly
            # positive literal weight on the entire residue ray. This
            # comparison therefore needs neither the source power nor a
            # geometric summary, even for a huge repetition count.
            return (
                (self.count, 0)
                if weight.numerator_scale == 0 and weight.numerator_offset == 0
                else (0, 0)
            )
        if weight.numerator_scale == 0:
            if charge is not None:
                charge(1)
            if charge_bits is not None:
                charge_bits(
                    weight.numerator_offset.bit_length()
                    + weight.denominator.bit_length()
                    + self.count.bit_length()
                    + transitions.bit_length()
                )
            per = weight.numerator_offset // weight.denominator
            if per == 0:
                if transitions:
                    raise ValueError("comma literal offset exceeds repeated return")
                return self.count, 0
            complete = min(self.count, transitions // per)
            remaining = transitions - complete * per
            if complete == self.count and remaining:
                raise ValueError("comma literal offset exceeds repeated return")
            return complete, remaining

        if charge is not None:
            charge(1)
        if charge_bits is not None:
            charge_bits(
                weight.numerator_offset.bit_length()
                + self.count.bit_length()
                + transitions.bit_length()
                + weight.denominator.bit_length()
            )
        minimum_constant = min(0, weight.numerator_offset * self.count)
        threshold = (transitions + 1) * weight.denominator - minimum_constant
        if exponent > threshold.bit_length():
            return 0, transitions
        if charge_bits is not None:
            charge_bits(4 * exponent + 1)
        source_scale = int(pow(10, exponent))
        a = weight.numerator_scale * source_scale
        if charge_bits is not None:
            charge_bits(weight.numerator_scale.bit_length() + source_scale.bit_length())
        geometric_cap = max(1, (threshold + a - 1) // a)
        delta = self.base.exponent_delta
        if delta == 0:
            # A zero-duration complete Q-return is the identity and has zero
            # weight under the action constructor invariant.
            if transitions:
                raise ValueError("comma literal offset exceeds repeated return")
            return self.count, 0
        if delta > geometric_cap.bit_length():
            radix = geometric_cap
        else:
            if charge_bits is not None:
                charge_bits(4 * delta + 1)
            radix = min(geometric_cap, int(pow(10, delta)))

        def capped_product(left: int, right: int) -> int:
            if charge_bits is not None:
                charge_bits(left.bit_length() + right.bit_length())
            return min(geometric_cap, left * right)

        def capped_sum(left: int, right: int) -> int:
            if charge_bits is not None:
                charge_bits(left.bit_length() + right.bit_length())
            return min(geometric_cap, left + right)

        def compose(
            first: SkewTransfer[int], second: SkewTransfer[int]
        ) -> SkewTransfer[int]:
            return first.then(second, multiply=capped_product, add=capped_sum)

        block = SkewTransfer(1, 1, radix)
        blocks: list[SkewTransfer[int]] = []
        for _ in range(self.count.bit_length()):
            if charge is not None:
                charge(1)
            blocks.append(block)
            block = compose(block, block)

        completed = 0
        prefix = SkewTransfer(1, 0, 1)
        for level in range(len(blocks) - 1, -1, -1):
            if charge is not None:
                charge(1)
            candidate_count = completed + (1 << level)
            if candidate_count > self.count:
                continue
            candidate = compose(prefix, blocks[level])
            candidate_sum = candidate.offset
            if candidate_sum == geometric_cap:
                continue
            if charge_bits is not None:
                charge_bits(
                    a.bit_length()
                    + candidate_sum.bit_length()
                    + weight.numerator_offset.bit_length()
                    + candidate_count.bit_length()
                )
            candidate_numerator = (
                a * candidate_sum + weight.numerator_offset * candidate_count
            )
            if candidate_numerator <= transitions * weight.denominator:
                completed = candidate_count
                prefix = candidate
        if charge_bits is not None:
            charge_bits(
                a.bit_length()
                + prefix.offset.bit_length()
                + weight.numerator_offset.bit_length()
                + completed.bit_length()
            )
        exact_numerator = a * prefix.offset + weight.numerator_offset * completed
        exact_weight, remainder = divmod(exact_numerator, weight.denominator)
        if remainder:
            raise ValueError("repeated comma prefix weight is not integral")
        residual = transitions - exact_weight
        if completed == self.count and residual:
            raise ValueError("comma literal offset exceeds repeated return")
        return completed, residual

    def weight_at(
        self,
        exponent: int,
        *,
        cap: int | None = None,
        charge: Callable[[int], None] | None = None,
        charge_bits: Callable[[int], None] | None = None,
    ) -> int:
        if (
            type(exponent) is not int
            or exponent < 5
            or exponent % PERIOD != self.base.start.exponent_residue
        ):
            raise ValueError("repeated comma return has another source exponent")
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("comma weight cap must be nonnegative")
        if self.count == 0:
            return 0
        weight = self.base.weight
        if cap == 0:
            if charge is not None:
                charge(1)
            return (
                0 if weight.numerator_scale == 0 and weight.numerator_offset == 0 else 1
            )
        if charge_bits is not None:
            charge_bits(
                weight.numerator_scale.bit_length()
                + weight.numerator_offset.bit_length()
                + self.count.bit_length()
                + exponent.bit_length()
            )
        b = weight.numerator_offset * self.count
        if weight.numerator_scale == 0:
            total, remainder = divmod(b, weight.denominator)
            if remainder:
                raise ValueError("repeated comma constant weight is not integral")
            return min(total, cap + 1) if cap is not None else total
        if cap is not None and weight.numerator_scale > 0:
            threshold = (cap + 1) * weight.denominator - b
            if threshold <= 0 or exponent > threshold.bit_length():
                return cap + 1
        if charge_bits is not None:
            charge_bits(4 * exponent + 1)
        scale = int(pow(10, exponent))
        if charge_bits is not None:
            charge_bits(scale.bit_length())
        a = weight.numerator_scale * scale
        if self.base.exponent_delta == 0:
            total, remainder = divmod(
                (a + weight.numerator_offset) * self.count, weight.denominator
            )
            if remainder:
                raise ValueError("repeated comma weight is not integral")
            return min(total, cap + 1) if cap is not None else total
        if cap is None:
            # Exact evaluation is output-sensitive; use a caller-supplied cap
            # for selection against a finite requested term index.
            if charge_bits is not None:
                charge_bits(4 * self.base.exponent_delta + 1)
            base = int(pow(10, self.base.exponent_delta))
            if charge_bits is not None:
                charge_bits(base.bit_length() * self.count)
            if charge is not None:
                charge(max(1, self.count.bit_length()))
            geometric = (int(pow(base, self.count)) - 1) // (base - 1)
        else:
            threshold = (cap + 1) * weight.denominator - b
            if threshold <= 0:
                return cap + 1
            geometric_cap = max(1, (threshold + a - 1) // a)
            if self.base.exponent_delta > geometric_cap.bit_length():
                base = geometric_cap
            else:
                if charge_bits is not None:
                    charge_bits(4 * self.base.exponent_delta + 1)
                base = min(geometric_cap, int(pow(10, self.base.exponent_delta)))
            geometric = _capped_geometric(
                base, self.count, geometric_cap, charge, charge_bits
            )
            if geometric >= geometric_cap:
                return cap + 1
        total, remainder = divmod(a * geometric + b, weight.denominator)
        if remainder:
            raise ValueError("repeated comma weight is not integral")
        return min(total, cap + 1) if cap is not None else total


__all__ = ["RepeatedBoundaryReturn", "WeightedBoundaryAction"]
