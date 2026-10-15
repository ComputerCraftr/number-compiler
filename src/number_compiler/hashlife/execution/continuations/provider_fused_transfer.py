"""Fused observation of canonical provider actions through family strategies.

Semantic provider actions are source independent. Exact source occurrences and
concrete boundary values enter only evictable bindings and one-entry response
memos. Family strategies absorb their consumer through canonical spatial
summaries; they never return future words or proof-machine states.
"""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import dataclass
from typing import Protocol

from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_operations import (
    evaluate_operation,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeAtom,
    RuntimeValueID,
)
from number_compiler.hashlife.execution.continuations.provider_absorption import (
    ProviderAbsorptionArena,
    ProviderAction,
    ProviderActionID,
    ProviderBindingKey,
    ProviderBoundary,
)
from number_compiler.hashlife.execution.field_images import SourceBindingID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys


@dataclass(frozen=True, slots=True)
class FusedProviderBinding:
    """Evictable occurrence binding for one semantic provider action."""

    occurrence: ProviderBindingKey


class ProviderFusedStrategy(Protocol):
    """Family implementation of bounded provider absorption."""

    ledger: ResourceLedger

    def point(
        self,
        binding: ProviderBindingKey,
        left: ProviderBoundary,
        right: ProviderBoundary,
        coordinate: int,
    ) -> int: ...

    def width(
        self,
        binding: ProviderBindingKey,
        left: ProviderBoundary,
        right: ProviderBoundary,
    ) -> int: ...


class HigherSummaryProviderStrategy:
    """Iterative ADV/RES/SECOND absorption through structural K/U summaries."""

    def __init__(
        self,
        providers: ProviderAbsorptionArena,
        runtime: HigherBimachineRuntime,
    ) -> None:
        if (
            providers.ledger is not runtime.ledger
            or providers.sources is not runtime.sources
        ):
            raise ValueError("higher provider strategy requires one index ledger")
        self.providers, self.runtime = providers, runtime
        self.ledger = runtime.ledger
        self.ledger.register_execution_root(self)

    def _boundary(
        self,
        binding: ProviderBindingKey,
        side: int,
        start: int,
        end: int,
    ) -> RuntimeAtom:
        action = self.providers.resolve(binding.provider).action
        incoming = evaluate_operation(
            self.runtime.semantics,
            "initial",
            action,
            side,
            (),
        )
        cells = self.runtime._range_cells(binding.source, start, end)
        ordered = cells if side == 0 else tuple(reversed(cells))
        if not ordered:
            return incoming
        summaries = self.runtime.summaries
        combined = summaries.combine_runtime_unary(
            tuple(summaries.runtime_unary(action, cell, side) for cell in ordered)
        )
        self.ledger.bump(_execution_keys.PROVIDER_FUSED_PARENT_TRANSFER_REQUESTS)
        # Keep the K application unforced.  The emit scheduler absorbs its
        # SECOND/RES continuation together with the opposite boundary; forcing
        # here would enumerate the composed concrete wreath state first.
        self.ledger.bump(_execution_keys.PROVIDER_FUSED_PARENT_TRANSFER_EVALUATIONS)
        return summaries.transfer_value(combined, incoming)

    def _canonical_exterior(
        self,
        binding: ProviderBindingKey,
        left: ProviderBoundary,
        right: ProviderBoundary,
    ) -> ProviderAction:
        record = self.providers.resolve(binding.provider)
        expected_left = evaluate_operation(
            self.runtime.semantics,
            "initial",
            record.action,
            0,
            (),
        )
        expected_right = evaluate_operation(
            self.runtime.semantics,
            "initial",
            record.action,
            1,
            (),
        )
        if left != expected_left or right != expected_right:
            raise ValueError(
                "higher provider received noncanonical exterior boundaries"
            )
        return record

    def point(
        self,
        binding: ProviderBindingKey,
        left: ProviderBoundary,
        right: ProviderBoundary,
        coordinate: int,
    ) -> int:
        record = self._canonical_exterior(binding, left, right)
        extent = self.runtime.sources.binding_extent(binding.source)
        if not 0 <= coordinate < extent:
            raise IndexError(coordinate)
        left_state = self._boundary(binding, 0, 0, coordinate)
        right_state = self._boundary(binding, 1, coordinate + 1, extent)
        symbol = self.runtime.sources.binding_read(binding.source, coordinate)
        result = evaluate_operation(
            self.runtime.semantics,
            "emit",
            record.action,
            -1,
            (left_state, symbol, right_state),
        )
        if type(result) is not int:
            raise AssertionError("fused provider output did not reduce to a symbol")
        self.ledger.bump(_shared_keys.OUTPUT_MORPHISM_VISITS)
        return result

    def width(
        self,
        binding: ProviderBindingKey,
        left: ProviderBoundary,
        right: ProviderBoundary,
    ) -> int:
        record = self._canonical_exterior(binding, left, right)
        extent = self.runtime.sources.binding_extent(binding.source)
        _base, blank = self.runtime.schema.alphabet(record.action)
        low, high = 0, extent
        while low < high:
            middle = (low + high) // 2
            if self.point(binding, left, right, middle) == blank:
                high = middle
            else:
                low = middle + 1
            self.ledger.bump(_execution_keys.SPATIAL_OBSERVATION_DESCENTS)
        return low


@dataclass(frozen=True, slots=True)
class _FusedPointKey:
    binding: FusedProviderBinding
    left: ProviderBoundary
    right: ProviderBoundary
    coordinate: int


@dataclass(frozen=True, slots=True)
class _FusedWidthKey:
    binding: FusedProviderBinding
    left: ProviderBoundary
    right: ProviderBoundary


class ProviderFusedTransfer:
    """Validate, memoize, and dispatch one fused family observation."""

    def __init__(
        self,
        providers: ProviderAbsorptionArena,
        strategy: ProviderFusedStrategy,
    ) -> None:
        if type(providers) is not ProviderAbsorptionArena:
            raise TypeError("fused transfer requires a provider arena")
        if strategy.ledger is not providers.ledger:
            raise ValueError("fused provider resources require one index ledger")
        self.providers, self.strategy = providers, strategy
        self.sources, self.ledger = providers.sources, providers.ledger
        self.ledger.register_execution_root(self)
        prefix = f"provider-fused-transfer-{len(self.ledger.inventory())}"
        self._binding_owner = self.ledger.register(
            prefix + "-bindings",
            "spatial_binding",
        )
        self._point_owner = self.ledger.register(
            prefix + "-points",
            "observation_memo",
        )
        self._width_owner = self.ledger.register(
            prefix + "-widths",
            "observation_memo",
        )
        self._bindings: MutableMapping[FusedProviderBinding, None] = (
            self.ledger.make_dict(self._binding_owner)
        )
        self._points: MutableMapping[_FusedPointKey, int] = self.ledger.make_dict(
            self._point_owner,
        )
        self._widths: MutableMapping[_FusedWidthKey, int] = self.ledger.make_dict(
            self._width_owner,
        )
        for owner, container in (
            (self._binding_owner, self._bindings),
            (self._point_owner, self._points),
            (self._width_owner, self._widths),
        ):
            self.ledger.register_container(
                owner,
                container,
                payloads=container.items,
                evict=self.clear,
            )

    def clear(self) -> None:
        for owner, container in (
            (self._binding_owner, self._bindings),
            (self._point_owner, self._points),
            (self._width_owner, self._widths),
        ):
            count = len(container)
            container.clear()
            self.ledger.release(owner, entries=count)

    def bind(
        self,
        provider: ProviderActionID,
        source: SourceBindingID,
        output: object,
        interface: object,
    ) -> FusedProviderBinding:
        from number_compiler.hashlife.actions.field_actions import (
            CoordinateOutputMorphismID,
        )
        from number_compiler.hashlife.interfaces.diamond_quotient import (
            LocalInterfaceID,
        )

        if type(output) is not CoordinateOutputMorphismID:
            raise TypeError("fused binding requires a coordinate output morphism")
        if type(interface) is not LocalInterfaceID:
            raise TypeError("fused binding requires a local interface")
        occurrence = self.providers.bind(provider, source, output, interface)
        binding = FusedProviderBinding(occurrence)
        if binding not in self._bindings:
            self.ledger.reserve(self._binding_owner, entries=1)
            self._bindings[binding] = None
            self.ledger.bump(_execution_keys.PROVIDER_FUSED_BINDING_PUBLICATIONS)
        else:
            self.ledger.bump(_execution_keys.PROVIDER_FUSED_BINDING_HITS)
        return binding

    def _validate(
        self,
        binding: FusedProviderBinding,
        left: ProviderBoundary,
        right: ProviderBoundary,
    ) -> ProviderBindingKey:
        if type(binding) is not FusedProviderBinding:
            raise TypeError("fused observation requires a scoped provider binding")
        # The nested scoped handles are authority; wrapper membership is only
        # an occurrence lookup.  Validate the authority before probing even a
        # warm wrapper cache so foreign or forged integer aliases cannot use
        # equality/hashing as an admission path.
        self.providers.validate_binding(binding.occurrence, left, right)
        if binding not in self._bindings:
            raise ValueError("fused provider binding was not published")
        return binding.occurrence

    def point(
        self,
        binding: FusedProviderBinding,
        left: ProviderBoundary,
        right: ProviderBoundary,
        coordinate: int,
    ) -> int:
        if type(coordinate) is not int:
            raise TypeError("fused coordinate must be an exact integer")
        occurrence = self._validate(binding, left, right)
        if not 0 <= coordinate < self.sources.binding_extent(occurrence.source):
            raise IndexError(coordinate)
        key = _FusedPointKey(binding, left, right, coordinate)
        self.ledger.bump(_execution_keys.PROVIDER_FUSED_POINT_REQUESTS)
        found = self._points.get(key)
        if found is not None:
            self.ledger.bump(_execution_keys.PROVIDER_FUSED_POINT_EARLY_HITS)
            return found
        result = self.strategy.point(occurrence, left, right, coordinate)
        if type(result) is not int:
            raise ValueError("fused point strategy returned another result sort")
        if self._points:
            count = len(self._points)
            self._points.clear()
            self.ledger.release(self._point_owner, entries=count)
        if type(left) is RuntimeValueID or type(right) is RuntimeValueID:
            self.ledger.bump(
                _execution_keys.PROVIDER_FUSED_POINT_UNCACHEABLE_BOUNDARIES
            )
            self.ledger.bump(_execution_keys.PROVIDER_FUSED_POINT_EVALUATIONS)
            return result
        self.ledger.reserve(self._point_owner, entries=1)
        self._points[key] = result
        self.ledger.bump(_execution_keys.PROVIDER_FUSED_POINT_EVALUATIONS)
        return result

    def width(
        self,
        binding: FusedProviderBinding,
        left: ProviderBoundary,
        right: ProviderBoundary,
    ) -> int:
        occurrence = self._validate(binding, left, right)
        key = _FusedWidthKey(binding, left, right)
        self.ledger.bump(_execution_keys.PROVIDER_FUSED_WIDTH_REQUESTS)
        found = self._widths.get(key)
        if found is not None:
            self.ledger.bump(_execution_keys.PROVIDER_FUSED_WIDTH_EARLY_HITS)
            return found
        result = self.strategy.width(occurrence, left, right)
        if type(result) is not int or result < 0:
            raise ValueError("fused width strategy returned another result sort")
        if self._widths:
            count = len(self._widths)
            self._widths.clear()
            self.ledger.release(self._width_owner, entries=count)
        if type(left) is RuntimeValueID or type(right) is RuntimeValueID:
            self.ledger.bump(
                _execution_keys.PROVIDER_FUSED_WIDTH_UNCACHEABLE_BOUNDARIES
            )
            self.ledger.bump(_execution_keys.PROVIDER_FUSED_WIDTH_EVALUATIONS)
            return result
        self.ledger.reserve(self._width_owner, entries=1)
        self._widths[key] = result
        self.ledger.bump(_execution_keys.PROVIDER_FUSED_WIDTH_EVALUATIONS)
        return result


__all__ = [
    "FusedProviderBinding",
    "HigherSummaryProviderStrategy",
    "ProviderFusedStrategy",
    "ProviderFusedTransfer",
]
