"""Exact tropical threshold pullbacks, without source or itinerary authority.

For positive affine prefix maps f_j, an input reaches below T iff it is below
max_j f_j^{-1}(T). This is also the ALL/above preimage of their minimum.
Normalization removes dominated lines, not the source admission obligation.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import (
    ZERO,
    affine_threshold_preimage,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational as Q,
)
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer


@dataclass(frozen=True, slots=True)
class ThresholdEnvelope:
    """Canonical upper hull over all real thresholds; no cached provenance."""

    lines: tuple[AffineCocycle[Q], ...]

    def __post_init__(self) -> None:
        lines = self.lines
        if type(lines) is not tuple:
            raise TypeError("threshold lines must be an immutable tuple")
        if len(lines) > 4096:
            raise BlockContextBudgetExceeded(
                "threshold line construction budget exceeded"
            )
        best: dict[Q, Q] = {}
        for line in lines:
            if (
                type(line) is not AffineCocycle
                or type(line.multiplier) is not Q
                or type(line.addend) is not Q
            ):
                raise TypeError("threshold lines require exact rational affine actions")
            line.multiplier.validate()
            line.addend.validate()
            if line.multiplier <= ZERO:
                raise ValueError("threshold lines require positive slope")
            old = best.get(line.multiplier)
            if old is None or line.addend > old:
                best[line.multiplier] = line.addend
        hull: list[tuple[AffineCocycle[Q], Q | None]] = []
        for slope, intercept in sorted(best.items()):
            start = None
            while hull:
                previous, previous_start = hull[-1]
                crossing = (previous.addend - intercept) / (slope - previous.multiplier)
                if previous_start is not None and crossing <= previous_start:
                    hull.pop()
                else:
                    start = crossing
                    break
            hull.append((AffineCocycle(slope, intercept), start))
        object.__setattr__(self, "lines", tuple(line for line, _ in hull))

    @classmethod
    def normalize(
        cls, lines: tuple[AffineCocycle[Q], ...], *, max_lines: int = 4096
    ) -> ThresholdEnvelope:
        if type(lines) is not tuple:
            raise TypeError("threshold lines must be an immutable tuple")
        if type(max_lines) is not int or not 1 <= max_lines <= 4096:
            raise ValueError("threshold line budget must lie in 1..4096")
        if len(lines) > max_lines:
            raise BlockContextBudgetExceeded(
                "threshold line construction budget exceeded"
            )
        return cls(lines)

    @classmethod
    def affine(cls, scale: Q, offset: Q) -> ThresholdEnvelope:
        """Inverse threshold action of one positive affine map."""
        inverse_offset = affine_threshold_preimage(scale, offset, ZERO)
        return cls.normalize((AffineCocycle(Q(1) / scale, inverse_offset),))

    def evaluate(self, threshold: Q) -> Q | None:
        """None denotes the empty event set, whose upper envelope is -infinity."""
        if type(threshold) is not Q:
            raise TypeError("threshold evaluation requires an exact rational")
        threshold.validate()
        return max(
            (line.multiplier * threshold + line.addend for line in self.lines),
            default=None,
        )

    def then(
        self,
        endpoint: SkewTransfer[int],
        after: ThresholdEnvelope,
        *,
        max_lines: int = 4096,
    ) -> ThresholdEnvelope:
        """NF(max(self, endpoint-preimage(after))), with chronological order."""
        if type(after) is not ThresholdEnvelope or type(endpoint) is not SkewTransfer:
            raise TypeError("threshold composition requires an envelope and skew")
        if any(
            type(x) is not int
            for x in (endpoint.upper, endpoint.offset, endpoint.lower)
        ):
            raise TypeError("threshold skew coefficients must be exact integers")
        if endpoint.upper <= 0 or endpoint.lower <= 0:
            raise ValueError("threshold pullback requires a positive affine skew")
        if type(max_lines) is not int or not 1 <= max_lines <= 4096:
            raise ValueError("threshold line budget must lie in 1..4096")
        if len(self.lines) + len(after.lines) > max_lines:
            raise BlockContextBudgetExceeded(
                "threshold line construction budget exceeded"
            )
        scale, offset = (
            Q(endpoint.upper, endpoint.lower),
            Q(endpoint.offset, endpoint.lower),
        )
        pulled = tuple(
            AffineCocycle(
                line.multiplier / scale,
                affine_threshold_preimage(scale, offset, line.addend),
            )
            for line in after.lines
        )
        return self.normalize((*self.lines, *pulled), max_lines=max_lines)
