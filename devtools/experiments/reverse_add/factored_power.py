"""Memoized temporal squaring of the exact three-plane successor.

The exponent is an execution coordinate. Squaring does not assert logarithmic
execution: unresolved Boolean/domain forcing still requires primitive steps.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.experiments.reverse_add.factored_carrier import (
    FactoredReverseCarrier,
    TemporalCell,
)
from devtools.experiments.reverse_add.factored_planes import PlaneID
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)
from number_compiler.arithmetic.polynomials.f5_transport import (
    F5AffineTransport,
    F5SpatialTransport,
)


@dataclass(frozen=True, slots=True)
class FactoredPowerBlock:
    """An exact source-bound segment, including its composed F5 affine action."""

    output: TemporalCell
    action: F5AffineTransport[PlaneID]


class FactoredTemporalPower:
    def __init__(
        self, carrier: FactoredReverseCarrier, *, max_entries: int = 16384
    ) -> None:
        require_endpoint_construction()
        if (
            type(carrier) is not FactoredReverseCarrier
            or type(max_entries) is not int
            or max_entries < 1
        ):
            raise ValueError(
                "factored powers require a carrier and positive cache budget"
            )
        self.carrier = carrier
        self.max_entries = max_entries
        self._memo: dict[tuple[TemporalCell, int], FactoredPowerBlock] = {}
        self.cache_hits = 0
        self.compositions = 0

    def _pad(self, plane: PlaneID, width: int) -> PlaneID:
        p = self.carrier.planes
        extra = width - p.resolve(plane, "f5").length
        if extra < 0:
            raise ValueError("affine composition cannot truncate an earlier field")
        return p.concat(plane, p.constant("f5", 0, extra)) if extra else plane

    def _compose(
        self,
        source: TemporalCell,
        before: FactoredPowerBlock,
        after: FactoredPowerBlock,
    ) -> FactoredPowerBlock:
        p = self.carrier.planes
        p.clear_work()
        try:
            width = p.resolve(after.output.f5).length
            earlier = F5AffineTransport(
                before.action.linear, self._pad(before.action.forcing, width)
            )
            action = earlier.then(
                after.action,
                shift=p.shift,
                add=self.carrier._add,
                scale=self.carrier._scale,
            )
            # Evaluate the accumulated homogeneous operator through Frobenius,
            # with the separately transported, source-bound forcing. Nonlinear
            # output channels still require the primitive path above this step.
            alpha = action.apply(
                self._pad(source.f5, width),
                shift=p.shift,
                add=self.carrier._add,
                scale=self.carrier._scale,
            )
            if alpha != after.output.f5:
                raise AssertionError(
                    "composed F5 action disagrees with its exact endpoint"
                )
            self.compositions += 1
            return FactoredPowerBlock(
                TemporalCell(after.output.domain, alpha, after.output.half), action
            )
        finally:
            p.clear_work()

    def block(self, source: TemporalCell, steps: int) -> FactoredPowerBlock:
        """Compile a segment; its forcing is valid only for this exact source."""
        require_endpoint_construction()
        if type(steps) is not int or steps < 0:
            raise ValueError("temporal exponent must be nonnegative")
        p = self.carrier.planes
        p.clear_work()
        try:
            self.carrier.validate(source)
        finally:
            p.clear_work()
        pending = [(source, steps, 0)]
        results: list[FactoredPowerBlock] = []
        while pending:
            cell, count, stage = pending.pop()
            key = cell, count
            found = self._memo.get(key)
            if found is not None:
                self.cache_hits += 1
                results.append(found)
                continue
            if stage == 1:
                midpoint = results[-1].output
                pending.append((cell, count, 2))
                pending.append((midpoint, count - count // 2, 0))
                continue
            if stage == 2:
                after = results.pop()
                before = results.pop()
                result = self._compose(cell, before, after)
            elif count == 0:
                result = FactoredPowerBlock(
                    cell,
                    F5AffineTransport(
                        F5SpatialTransport(),
                        p.constant("f5", 0, p.resolve(cell.f5).length),
                    ),
                )
            elif count == 1:
                output, _, action = self.carrier.successor_with_action(cell)
                result = FactoredPowerBlock(output, action)
            else:
                pending.append((cell, count, 1))
                pending.append((cell, count // 2, 0))
                continue
            if len(self._memo) >= self.max_entries:
                raise BlockContextBudgetExceeded(
                    "factored temporal execution cache exhausted"
                )
            self._memo[key] = result
            results.append(result)
        if len(results) != 1:
            raise AssertionError("temporal composition lost its result")
        return results[0]

    def advance(self, source: TemporalCell, steps: int) -> TemporalCell:
        return self.block(source, steps).output

    def clear(self) -> None:
        self._memo.clear()
