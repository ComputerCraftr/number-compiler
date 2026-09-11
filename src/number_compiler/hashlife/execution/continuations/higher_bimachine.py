"""Iterative execution of recursively typed, binary-composed bimachines.

The temporal action is source independent.  Original source cells are bound
only by evictable spatial transfer memos.  A point observation composes
canonical transfer functions over a logarithmic dyadic cover and never emits
an intermediate word.
"""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_operations import (
    evaluate_operation,
    force_value,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_summaries import (
    HigherSummaryArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
    HigherFunctionID,
)
from number_compiler.hashlife.execution.continuations.higher_values import RuntimeAtom
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class _Initial:
    action: FieldCellActionID
    side: int


@dataclass(frozen=True, slots=True)
class _Step:
    action: FieldCellActionID
    side: int
    state: HigherExpressionID
    symbol: HigherExpressionID


@dataclass(frozen=True, slots=True)
class _Emit:
    action: FieldCellActionID
    left: HigherExpressionID
    symbol: HigherExpressionID
    right: HigherExpressionID


_Operation = _Initial | _Step | _Emit


@dataclass(frozen=True, slots=True)
class _Transfer:
    action: FieldCellActionID
    source: SourceCellID
    side: int


class HigherBimachineRuntime:
    """Demand evaluator for one scoped action/schema/source collection."""

    def __init__(
        self, semantics: HigherSemanticArena, sources: SourceCellArena
    ) -> None:
        if semantics.ledger is not sources.ledger:
            raise ValueError("higher bimachine requires one index ledger")
        self.semantics = semantics
        self.schema = semantics.schema
        self.sources = sources
        self.ledger: ResourceLedger = sources.ledger
        self.owner = ArenaToken("higher-bimachine-runtime")
        self.ledger.register_execution_root(self)
        self.summaries = HigherSummaryArena(semantics, sources)
        semantics.bind_summary_runtime(self.summaries)
        prefix = f"higher-bimachine-{len(self.ledger.inventory())}"
        self._operation_owner = self.ledger.register(
            prefix + "-operations",
            "query_memo",
        )
        self._transfer_owner = self.ledger.register(
            prefix + "-transfers",
            "query_memo",
        )
        self._operations: MutableMapping[_Operation, HigherExpressionID] = (
            self.ledger.make_dict(self._operation_owner)
        )
        self._transfers: MutableMapping[_Transfer, HigherFunctionID] = (
            self.ledger.make_dict(self._transfer_owner)
        )
        self.ledger.register_container(
            self._operation_owner,
            self._operations,
            payloads=self._operations.items,
            evict=self.clear,
        )
        self.ledger.register_container(
            self._transfer_owner,
            self._transfers,
            payloads=self._transfers.items,
            evict=self.clear,
        )

    def clear(self) -> None:
        operation_count, transfer_count = len(self._operations), len(self._transfers)
        self._operations.clear()
        self._transfers.clear()
        self.ledger.release(self._operation_owner, entries=operation_count)
        self.ledger.release(self._transfer_owner, entries=transfer_count)

    def _publish_operation(
        self,
        task: _Operation,
        result: HigherExpressionID,
        built: MutableMapping[_Operation, HigherExpressionID],
    ) -> None:
        self.ledger.reserve(self._operation_owner, entries=1)
        self._operations[task] = result
        built[task] = result
        self.ledger.bump("opaque_higher_operation_publications")

    def _operation(self, root: _Operation) -> HigherExpressionID:
        found = self._operations.get(root)
        if found is not None:
            self.ledger.bump("higher_operation_early_hits")
            return found
        published: dict[_Operation, HigherExpressionID] = {}
        if isinstance(root, _Initial):
            result = self.semantics.action_initial(root.action, root.side)
        elif isinstance(root, _Step):
            result = self.semantics.action_step(
                root.action,
                root.side,
                root.state,
                root.symbol,
            )
        else:
            result = self.semantics.action_emit(
                root.action,
                root.left,
                root.symbol,
                root.right,
            )
        self._publish_operation(root, result, published)
        return result

    def initial(self, action: FieldCellActionID, side: int) -> HigherExpressionID:
        self.schema.validate_action(action)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("higher boundary side must be zero or one")
        return self._operation(_Initial(action, side))

    def step(
        self,
        action: FieldCellActionID,
        side: int,
        state: HigherExpressionID,
        symbol: HigherExpressionID,
    ) -> HigherExpressionID:
        self.schema.validate_action(action)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("higher boundary side must be zero or one")
        self.semantics.expression(state)
        self.semantics.expression(symbol)
        return self._operation(_Step(action, side, state, symbol))

    def emit(
        self,
        action: FieldCellActionID,
        left: HigherExpressionID,
        symbol: HigherExpressionID,
        right: HigherExpressionID,
    ) -> HigherExpressionID:
        self.schema.validate_action(action)
        self.semantics.expression(left)
        self.semantics.expression(symbol)
        self.semantics.expression(right)
        return self._operation(_Emit(action, left, symbol, right))

    def transfer(
        self,
        action: FieldCellActionID,
        source: SourceCellID,
        side: int,
    ) -> HigherFunctionID:
        self.schema.validate_action(action)
        self.sources.resolve(source)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("higher transfer side must be zero or one")
        root = _Transfer(action, source, side)
        found = self._transfers.get(root)
        if found is not None:
            self.ledger.bump("higher_spatial_transfer_early_hits")
            return found
        stack: list[tuple[SourceCellID, bool]] = [(source, False)]
        built: dict[int, HigherFunctionID] = {}
        while stack:
            current, ready = stack.pop()
            key = _Transfer(action, current, side)
            cached = self._transfers.get(key)
            if cached is not None:
                built[current.local_id] = cached
                continue
            node = self.sources.resolve(current)
            if node.level and not ready:
                left, right = self.sources.children(current)
                stack.append((current, True))
                if right.local_id not in built:
                    stack.append((right, False))
                if left.local_id not in built:
                    stack.append((left, False))
                continue
            variable = self.semantics.variable(
                self.semantics.state_sort(action, side),
                f"higher-spatial-input:{action.local_id}:{side}",
            )
            if node.level == 0:
                symbol = self.semantics.symbol(action, self.sources.symbol(current))
                body = self.step(action, side, variable, symbol)
            else:
                left, right = self.sources.children(current)
                first, second = (left, right) if side == 0 else (right, left)
                first_fn = self.semantics.function_expression(built[first.local_id])
                second_fn = self.semantics.function_expression(built[second.local_id])
                body = self.semantics.apply(
                    second_fn,
                    self.semantics.apply(first_fn, variable),
                )
            result = self.semantics.function(variable, body)
            self.ledger.reserve(self._transfer_owner, entries=1)
            self._transfers[key] = result
            built[current.local_id] = result
            self.ledger.bump("higher_spatial_transfer_publications")
        return built[source.local_id]

    def _range_cells(
        self,
        source: SourceBindingID,
        start: int,
        end: int,
    ) -> tuple[SourceCellID, ...]:
        extent = self.sources.binding_extent(source)
        if any(type(value) is not int for value in (start, end)):
            raise TypeError("higher range coordinates must be exact integers")
        if not 0 <= start <= end <= extent:
            raise ValueError("higher range lies outside the source binding")
        if type(source) is SourceCellID:
            roots: tuple[SourceCellID, ...] = (source,)
        else:
            if type(source) is not SourceForestID:
                raise TypeError("higher range requires a scoped source binding")
            roots = self.sources.resolve_forest(source).cells
        result: list[tuple[int, SourceCellID]] = []
        offset = 0
        for root in roots:
            width = self.sources.resolve(root).width
            low, high = max(start, offset), min(end, offset + width)
            if low < high:
                stack = [(root, offset)]
                while stack:
                    current, origin = stack.pop()
                    node = self.sources.resolve(current)
                    finish = origin + node.width
                    if finish <= low or high <= origin:
                        continue
                    if low <= origin and finish <= high:
                        result.append((origin, current))
                        continue
                    left, right = self.sources.children(current)
                    middle = origin + self.sources.resolve(left).width
                    stack.extend(((right, middle), (left, origin)))
            offset += width
        result.sort(key=lambda item: item[0])
        self.ledger.bump("higher_range_dyadic_cells", len(result))
        return tuple(cell for _, cell in result)

    def _summary_boundary(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        side: int,
        start: int,
        end: int,
    ) -> HigherExpressionID:
        state = self.semantics.initial(action, side)
        cells = self._range_cells(source, start, end)
        ordered = cells if side == 0 else tuple(reversed(cells))
        for cell in ordered:
            state = self.summaries.apply_unary(
                self.summaries.unary(action, cell, side),
                state,
            )
        return state

    def _context_boundary(
        self,
        provider: FieldCellActionID,
        consumer: FieldCellActionID,
        source: SourceBindingID,
        side: int,
        start: int,
        end: int,
        provider_left: HigherExpressionID,
        provider_right: HigherExpressionID,
    ) -> HigherExpressionID:
        incoming = self.semantics.initial(consumer, side)
        cells = self._range_cells(source, start, end)
        if not cells:
            return incoming
        contexts = tuple(
            self.summaries.context(provider, consumer, cell) for cell in cells
        )
        forward = tuple(self.summaries.unary(provider, cell, 0) for cell in cells)
        backward = tuple(self.summaries.unary(provider, cell, 1) for cell in cells)
        summary = self.summaries.combine_context(contexts, forward, backward)
        return self.summaries.apply_context(
            summary,
            provider_left,
            provider_right,
            incoming,
            side,
        )

    def boundary(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        side: int,
        start: int,
        end: int,
    ) -> HigherExpressionID:
        state = self.initial(action, side)
        cells = self._range_cells(source, start, end)
        ordered = cells if side == 0 else tuple(reversed(cells))
        for cell in ordered:
            state = self.semantics.apply(
                self.semantics.function_expression(self.transfer(action, cell, side)),
                state,
            )
        return state

    def point(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        coordinate: int,
    ) -> int:
        self.ledger.bump("higher_point_observations")
        self.ledger.bump("higher_observation_fallback")
        extent = self.sources.binding_extent(source)
        if type(coordinate) is not int or not 0 <= coordinate < extent:
            raise IndexError(coordinate)
        children = self.schema.children(action)
        if children is None:
            left = self.boundary(action, source, 0, 0, coordinate)
            right = self.boundary(action, source, 1, coordinate + 1, extent)
            symbol = self.semantics.symbol(
                action,
                self.sources.binding_read(source, coordinate),
            )
            output = self.emit(action, left, symbol, right)
        else:
            before, after = children
            left_before = self._summary_boundary(before, source, 0, 0, coordinate)
            right_before = self._summary_boundary(
                before,
                source,
                1,
                coordinate + 1,
                extent,
            )
            original = self.semantics.symbol(
                before,
                self.sources.binding_read(source, coordinate),
            )
            left_after_symbol = self.step(before, 0, left_before, original)
            right_before_symbol = self.step(before, 1, right_before, original)
            left = self._context_boundary(
                before,
                after,
                source,
                0,
                0,
                coordinate,
                self.semantics.initial(before, 0),
                right_before_symbol,
            )
            right = self._context_boundary(
                before,
                after,
                source,
                1,
                coordinate + 1,
                extent,
                left_after_symbol,
                self.semantics.initial(before, 1),
            )
            middle = self.emit(before, left_before, original, right_before)
            output = self.emit(after, left, middle, right)
        value = self.semantics.evaluate(output)
        if type(value) is not int:
            raise AssertionError("higher output did not reduce to a scalar symbol")
        self.ledger.bump("output_morphism_visits")
        return value

    def _runtime_boundary(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        side: int,
        start: int,
        end: int,
    ) -> RuntimeAtom:
        state = evaluate_operation(self.semantics, "initial", action, side, ())
        cells = self._range_cells(source, start, end)
        ordered = cells if side == 0 else tuple(reversed(cells))
        if not ordered:
            return state
        summary = self.summaries.combine_runtime_unary(
            tuple(self.summaries.runtime_unary(action, cell, side) for cell in ordered)
        )
        return force_value(
            self.semantics,
            self.summaries.transfer_value(summary, state),
        )

    def runtime_boundary(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        side: int,
        start: int,
        end: int,
    ) -> RuntimeAtom:
        """Expose the validated structural boundary used by K/U observers."""
        self.schema.validate_action(action)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("higher boundary side must be zero or one")
        return self._runtime_boundary(action, source, side, start, end)

    def point_structural(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        coordinate: int,
    ) -> int:
        """Observe a point through canonical K summaries, without syntax replay."""
        self.ledger.bump("higher_point_observations")
        extent = self.sources.binding_extent(source)
        if type(coordinate) is not int or not 0 <= coordinate < extent:
            raise IndexError(coordinate)
        left = self._runtime_boundary(action, source, 0, 0, coordinate)
        right = self._runtime_boundary(action, source, 1, coordinate + 1, extent)
        symbol = self.sources.binding_read(source, coordinate)
        result = evaluate_operation(
            self.semantics,
            "emit",
            action,
            -1,
            (left, symbol, right),
        )
        if type(result) is not int:
            raise AssertionError("structural higher output did not reduce to a symbol")
        self.ledger.bump("output_morphism_visits")
        return result

    def width_structural(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
    ) -> int:
        """Find the active extent through logarithmic structural observations."""
        self.ledger.bump("higher_width_observations")
        extent = self.sources.binding_extent(source)
        _base, blank = self.schema.alphabet(action)
        low, high = 0, extent
        while low < high:
            middle = (low + high) // 2
            if self.point_structural(action, source, middle) == blank:
                high = middle
            else:
                low = middle + 1
            self.ledger.bump("spatial_observation_descents")
        return low

    def width(self, action: FieldCellActionID, source: SourceBindingID) -> int:
        self.ledger.bump("higher_width_observations")
        self.ledger.bump("higher_observation_fallback")
        extent = self.sources.binding_extent(source)
        _base, blank = self.schema.alphabet(action)
        low, high = 0, extent
        while low < high:
            middle = (low + high) // 2
            if self.point(action, source, middle) == blank:
                high = middle
            else:
                low = middle + 1
            self.ledger.bump("spatial_observation_descents")
        return low


__all__ = ["HigherBimachineRuntime"]
