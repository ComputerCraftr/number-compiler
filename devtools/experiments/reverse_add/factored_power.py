"""Memoized temporal squaring of the exact three-plane successor.

The exponent is an execution coordinate. Squaring does not assert logarithmic
execution: unresolved Boolean/domain forcing still requires primitive steps.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, Protocol, TypeVar, cast

from devtools.experiments.reverse_add.cocycle_carrier import (
    CocycleCell,
    CocycleReverseCarrier,
)
from devtools.experiments.reverse_add.factored_carrier import (
    FactoredReverseCarrier,
    TemporalCell,
)
from devtools.experiments.reverse_add.factored_planes import PlaneAlgebra, PlaneID
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)
from number_compiler.arithmetic.polynomials.f5_transport import (
    F5AffineTransport,
    F5SpatialTransport,
)

Cell = TypeVar("Cell", TemporalCell, CocycleCell)


class _Carrier(Protocol[Cell]):
    planes: PlaneAlgebra

    def validate(self, cell: Cell) -> int: ...
    def successor_with_emission(
        self, cell: Cell
    ) -> tuple[Cell, int, F5AffineTransport[PlaneID], tuple[PlaneID, PlaneID]]: ...
    def successor(self, cell: Cell) -> tuple[Cell, int]: ...
    def _add(self, left: PlaneID, right: PlaneID) -> PlaneID: ...
    def _scale(self, plane: PlaneID, scalar: int) -> PlaneID: ...


@dataclass(frozen=True, slots=True)
class FactoredPowerBlock(Generic[Cell]):
    """An exact source-bound segment, including its composed F5 affine action."""

    output: Cell
    action: F5AffineTransport[PlaneID]
    emission: tuple[PlaneID, PlaneID] | None = None


class FactoredTemporalPower(Generic[Cell]):
    def __init__(self, carrier: _Carrier[Cell], *, max_entries: int = 16384) -> None:
        require_endpoint_construction()
        if (
            type(carrier) not in (FactoredReverseCarrier, CocycleReverseCarrier)
            or type(max_entries) is not int
            or max_entries < 1
        ):
            raise ValueError(
                "factored powers require a carrier and positive cache budget"
            )
        self.carrier: _Carrier[Cell] = carrier
        self.max_entries = max_entries
        self._memo: dict[tuple[Cell, int], FactoredPowerBlock[Cell]] = {}
        # Endpoint requests cannot make a complete affine action authoritative.
        # They share the postorder driver but retain only exact output cells.
        self._endpoint_memo: dict[tuple[Cell, int], Cell] = {}
        self.cache_hits = 0
        self.compositions = 0
        self.endpoint_publications = 0

    def _pad(self, plane: PlaneID, width: int) -> PlaneID:
        p = self.carrier.planes
        extra = width - p.resolve(plane, "f5").length
        if extra < 0:
            raise ValueError("affine composition cannot truncate an earlier field")
        return p.concat(plane, p.constant("f5", 0, extra)) if extra else plane

    def _compose(
        self,
        source: Cell,
        before: FactoredPowerBlock[Cell],
        after: FactoredPowerBlock[Cell],
    ) -> FactoredPowerBlock[Cell]:
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
            # The right block already returned the exact grammar. Reapplying
            # the entire accumulated action here repeats source-to-output work
            # at every internal node. Affine equality is checked independently
            # in the differential tests, not used as a second constructor.
            if width != p.resolve(source.f5).length + action.linear.growths:
                raise ValueError("composed action has inconsistent source extent")
            self.compositions += 1
            return FactoredPowerBlock(after.output, action, after.emission)
        finally:
            p.clear_work()

    @staticmethod
    def _output(result: FactoredPowerBlock[Cell] | Cell) -> Cell:
        return result.output if isinstance(result, FactoredPowerBlock) else result

    def _construct(
        self, source: Cell, steps: int, *, complete: bool
    ) -> FactoredPowerBlock[Cell] | Cell:
        """One postorder driver with separate complete and endpoint authority."""
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
        results: list[FactoredPowerBlock[Cell] | Cell] = []
        memo = self._memo if complete else self._endpoint_memo
        while pending:
            cell, count, stage = pending.pop()
            key = cell, count
            found = memo.get(key)
            if found is not None:
                self.cache_hits += 1
                results.append(found)
                continue
            if not complete:
                complete_found = self._memo.get(key)
                if complete_found is not None:
                    self.cache_hits += 1
                    results.append(complete_found.output)
                    continue
            if stage == 1:
                midpoint = self._output(results[-1])
                pending.append((cell, count, 2))
                pending.append(
                    (midpoint, count - (1 << ((count - 1).bit_length() - 1)), 0)
                )
                continue
            if stage == 2:
                after = results.pop()
                before = results.pop()
                result = (
                    self._compose(
                        cell,
                        cast(FactoredPowerBlock[Cell], before),
                        cast(FactoredPowerBlock[Cell], after),
                    )
                    if complete
                    else self._output(after)
                )
            elif count == 0:
                result = (
                    FactoredPowerBlock(
                        cell,
                        F5AffineTransport(
                            F5SpatialTransport(),
                            p.constant("f5", 0, p.resolve(cell.f5).length),
                        ),
                    )
                    if complete
                    else cell
                )
            elif count <= 4:
                # J4 is an endpoint-free base on the *native plane grammar*.
                # Its four nonlinear advances remain measured work; binary
                # composition above it must not be reported as temporal pumping.
                prefix = 0
                for earlier_count in range(count - 1, 0, -1):
                    earlier_block = memo.get((cell, earlier_count))
                    if earlier_block is not None:
                        result = earlier_block
                        prefix = earlier_count
                        self.cache_hits += 1
                        break
                if not prefix:
                    if complete:
                        first_output, _, first_action, emission = (
                            self.carrier.successor_with_emission(cell)
                        )
                        result = FactoredPowerBlock(
                            first_output, first_action, emission
                        )
                    else:
                        result, _ = self.carrier.successor(cell)
                    prefix = 1
                for _ in range(prefix, count):
                    if complete:
                        output, _, action, emission = (
                            self.carrier.successor_with_emission(self._output(result))
                        )
                        result = self._compose(
                            cell,
                            cast(FactoredPowerBlock[Cell], result),
                            FactoredPowerBlock(output, action, emission),
                        )
                    else:
                        result, _ = self.carrier.successor(self._output(result))
            else:
                pending.append((cell, count, 1))
                pending.append((cell, 1 << ((count - 1).bit_length() - 1), 0))
                continue
            if len(self._memo) + len(self._endpoint_memo) >= self.max_entries:
                raise BlockContextBudgetExceeded(
                    "factored temporal execution cache exhausted"
                )
            if complete:
                self._memo[key] = cast(FactoredPowerBlock[Cell], result)
            else:
                self._endpoint_memo[key] = self._output(result)
                self.endpoint_publications += 1
            results.append(result)
        if len(results) != 1:
            raise AssertionError("temporal composition lost its result")
        return results[0]

    def block(self, source: Cell, steps: int) -> FactoredPowerBlock[Cell]:
        """Compile a segment; its forcing is valid only for this exact source."""
        return cast(
            FactoredPowerBlock[Cell], self._construct(source, steps, complete=True)
        )

    def advance(self, source: Cell, steps: int) -> Cell:
        return self._output(self._construct(source, steps, complete=False))

    def clear(self) -> None:
        self._memo.clear()
        self._endpoint_memo.clear()
