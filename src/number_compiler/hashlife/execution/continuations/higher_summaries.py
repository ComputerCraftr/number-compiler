"""Canonical K/U summaries for recursively composed field actions.

The records in this module are source independent semantic functions.  Exact
source cells occur only in the evictable binding maps used while compiling a
summary.  K and U are built iteratively and contain expression/function IDs,
never source digits, future words, or proof-machine states.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass, field

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.radix_transfer import RadixRemainderTransfer
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_input import (
    InputCellGeometry,
    RuntimeInputCellID,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
    HigherFunctionID,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeAtom,
    RuntimeTransferredState,
    RuntimeValueID,
)
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class HigherSummaryID(ArenaHandle):
    """Scoped canonical K/U semantic summary."""


@dataclass(frozen=True, slots=True)
class UnarySummary:
    action: FieldCellActionID
    side: int
    function: HigherFunctionID
    recipe: UnaryRecipe = field(compare=False, hash=False)


@dataclass(frozen=True, slots=True)
class ContextSummary:
    provider: FieldCellActionID
    consumer: FieldCellActionID
    left: HigherExpressionID
    right: HigherExpressionID
    incoming_left: HigherExpressionID
    incoming_right: HigherExpressionID
    left_body: HigherExpressionID
    right_body: HigherExpressionID
    recipe: ContextRecipe = field(compare=False, hash=False)


@dataclass(frozen=True, slots=True)
class UnaryLeaf:
    symbol: int


@dataclass(frozen=True, slots=True)
class UnaryIdentity:
    pass


@dataclass(frozen=True, slots=True)
class UnaryFinite:
    """Complete bounded primitive port function, never an emitted tape."""

    outputs: tuple[int, ...]

    def __post_init__(self) -> None:
        if (
            type(self.outputs) is not tuple
            or not 1 <= len(self.outputs) <= 64
            or any(
                type(value) is not int or not 0 <= value < len(self.outputs)
                for value in self.outputs
            )
        ):
            raise ValueError("finite unary transfer has an invalid bounded port")


@dataclass(frozen=True, slots=True)
class UnaryAffine:
    """A bounded modular port action; its payload never grows with cell width."""

    transfer: RadixRemainderTransfer


@dataclass(frozen=True, slots=True)
class UnarySpatial:
    first: HigherSummaryID
    second: HigherSummaryID


@dataclass(frozen=True, slots=True)
class UnaryTemporal:
    forward: HigherSummaryID
    opposite: HigherSummaryID
    context: HigherSummaryID


UnaryRecipe = (
    UnaryIdentity | UnaryFinite | UnaryAffine | UnaryLeaf | UnarySpatial | UnaryTemporal
)


@dataclass(frozen=True, slots=True)
class ContextLeaf:
    symbol: int


@dataclass(frozen=True, slots=True)
class ContextSpatial:
    low: HigherSummaryID
    high: HigherSummaryID
    low_forward: HigherSummaryID
    high_backward: HigherSummaryID


ContextRecipe = ContextLeaf | ContextSpatial


@dataclass(frozen=True, slots=True)
class RuntimeUnarySummary:
    action: FieldCellActionID
    side: int
    recipe: UnaryRecipe


@dataclass(frozen=True, slots=True)
class RuntimeContextSummary:
    provider: FieldCellActionID
    consumer: FieldCellActionID
    recipe: ContextRecipe


SummaryRecord = (
    UnarySummary | ContextSummary | RuntimeUnarySummary | RuntimeContextSummary
)


@dataclass(frozen=True, slots=True)
class _UnaryBinding:
    action: FieldCellActionID
    source: RuntimeInputCellID
    side: int


@dataclass(frozen=True, slots=True)
class _ContextBinding:
    provider: FieldCellActionID
    consumer: FieldCellActionID
    source: RuntimeInputCellID


class HigherSummaryArena:
    """Iterative source binding and semantic interning for K/U closures."""

    _UNARY_KIND = "higher-unary-summary"
    _CONTEXT_KIND = "higher-context-summary"

    def __init__(
        self,
        semantics: HigherSemanticArena,
        sources: SourceCellArena,
    ) -> None:
        if semantics.ledger is not sources.ledger:
            raise ValueError("higher summaries require one index ledger")
        self.semantics = semantics
        self.schema = semantics.schema
        self.sources = sources
        self.ledger: ResourceLedger = semantics.ledger
        self.owner = ArenaToken("higher-summary")
        self.ledger.register_execution_root(self)
        prefix = f"higher-summary-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(
            prefix + "-nodes", "macro_transfer_program"
        )
        self._key_owner = self.ledger.register(
            prefix + "-interner",
            "macro_transfer_program_interner",
        )
        self._binding_owner = self.ledger.register(
            prefix + "-bindings", "spatial_parent_memo"
        )
        self._runtime_binding_owner = self.ledger.register(
            prefix + "-runtime-bindings",
            "spatial_parent_memo",
        )
        self._runtime_composition_owner = self.ledger.register(
            prefix + "-runtime-compositions",
            "spatial_parent_memo",
        )
        self._runtime_compositions: MutableMapping[
            tuple[HigherSummaryID, HigherSummaryID], HigherSummaryID
        ] = self.ledger.make_dict(self._runtime_composition_owner)
        self.ledger.register_container(
            self._runtime_composition_owner,
            self._runtime_compositions,
            payloads=self._runtime_compositions.items,
            evict=self.clear_bindings,
        )
        self._blank_identity_owner = self.ledger.register(
            prefix + "-blank-identities",
            "query_memo",
        )
        self._nodes: MutableSequence[SummaryRecord] = self.ledger.make_list(
            self._node_owner
        )
        self._keys: MutableMapping[SummaryRecord, int] = self.ledger.make_dict(
            self._key_owner
        )
        self._bindings: MutableMapping[
            _UnaryBinding | _ContextBinding, HigherSummaryID
        ] = self.ledger.make_dict(self._binding_owner)
        self._runtime_bindings: MutableMapping[
            _UnaryBinding | _ContextBinding, HigherSummaryID
        ] = self.ledger.make_dict(self._runtime_binding_owner)
        self._blank_identity: MutableMapping[tuple[FieldCellActionID, int], bool] = (
            self.ledger.make_dict(self._blank_identity_owner)
        )
        self.ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=lambda: self._nodes,
        )
        self.ledger.register_container(
            self._key_owner,
            self._keys,
            payloads=self._keys.items,
        )
        self.ledger.register_container(
            self._binding_owner,
            self._bindings,
            payloads=self._bindings.items,
            evict=self.clear_bindings,
        )
        self.semantics.runtime_values.bind_summary_validator(self.resolve)
        self.ledger.register_container(
            self._runtime_binding_owner,
            self._runtime_bindings,
            payloads=self._runtime_bindings.items,
            evict=self.clear_bindings,
        )
        self.ledger.register_container(
            self._blank_identity_owner,
            self._blank_identity,
            payloads=self._blank_identity.items,
            evict=self.clear_bindings,
        )

    def validate_input(self, cell: RuntimeInputCellID) -> None:
        if type(cell) is not SourceCellID:
            raise TypeError("summary input requires an issued source cell")
        self.sources.resolve(cell)

    def _input_geometry(self, cell: RuntimeInputCellID) -> InputCellGeometry:
        self.validate_input(cell)
        node = self.sources.resolve(cell)
        return InputCellGeometry(node.level, node.uniform_symbol)

    def _input_children(
        self, cell: RuntimeInputCellID
    ) -> tuple[RuntimeInputCellID, RuntimeInputCellID]:
        self.validate_input(cell)
        return self.sources.children(cell)

    def _input_symbol(self, cell: RuntimeInputCellID) -> int:
        self.validate_input(cell)
        return self.sources.symbol(cell)

    def clear_bindings(self) -> None:
        composition_count = len(self._runtime_compositions)
        self._runtime_compositions.clear()
        self.ledger.release(self._runtime_composition_owner, entries=composition_count)
        count = len(self._bindings)
        runtime_count = len(self._runtime_bindings)
        identity_count = len(self._blank_identity)
        self._bindings.clear()
        self._runtime_bindings.clear()
        self._blank_identity.clear()
        self.ledger.release(self._binding_owner, entries=count)
        self.ledger.release(self._runtime_binding_owner, entries=runtime_count)
        self.ledger.release(self._blank_identity_owner, entries=identity_count)

    def _handle(self, local_id: int, record: SummaryRecord) -> HigherSummaryID:
        kind = (
            self._UNARY_KIND
            if type(record) in (UnarySummary, RuntimeUnarySummary)
            else self._CONTEXT_KIND
        )
        return HigherSummaryID(self.owner, kind, local_id)

    def resolve(self, reference: HigherSummaryID) -> SummaryRecord:
        if type(reference) is not HigherSummaryID:
            raise TypeError("expected a scoped higher summary ID")
        if reference.kind not in (self._UNARY_KIND, self._CONTEXT_KIND):
            raise ValueError("higher summary has the wrong handle kind")
        reference.validate(self.owner, reference.kind, size=len(self._nodes))
        record = self._nodes[reference.local_id]
        if (reference.kind == self._UNARY_KIND) != (
            type(record) in (UnarySummary, RuntimeUnarySummary)
        ):
            raise ValueError("higher summary handle kind disagrees with its record")
        return record

    def unary_record(self, reference: HigherSummaryID) -> UnarySummary:
        record = self.resolve(reference)
        if type(record) is not UnarySummary:
            raise ValueError("expected a unary higher summary")
        return record

    def runtime_unary_record(self, reference: HigherSummaryID) -> RuntimeUnarySummary:
        record = self.resolve(reference)
        if type(record) is not RuntimeUnarySummary:
            raise ValueError("expected a runtime-only unary summary")
        return record

    def context_record(self, reference: HigherSummaryID) -> ContextSummary:
        record = self.resolve(reference)
        if type(record) is not ContextSummary:
            raise ValueError("expected a context higher summary")
        return record

    def runtime_context_record(
        self,
        reference: HigherSummaryID,
    ) -> RuntimeContextSummary:
        record = self.resolve(reference)
        if type(record) is not RuntimeContextSummary:
            raise ValueError("expected a runtime-only context summary")
        return record

    def transfer_value(
        self,
        summary: HigherSummaryID,
        incoming: RuntimeAtom,
    ) -> RuntimeAtom:
        """Bind one K summary without expanding its spatial or temporal body."""
        record = self.runtime_unary_record(summary)
        values = self.semantics.runtime_values
        incoming = values.canonical_atom(incoming)
        if type(incoming) is int and (
            self.schema.children(record.action) is not None
            or not 0 <= incoming < self.schema.state_count(record.action, record.side)
        ):
            raise ValueError("summary input is outside its action port")
        if type(record.recipe) is UnaryIdentity:
            self.ledger.bump("higher_identity_transfer_elisions")
            return incoming
        if type(record.recipe) is UnaryFinite and type(incoming) is int:
            self.ledger.bump("higher_finite_transfer_state_visits")
            return record.recipe.outputs[incoming]
        if type(record.recipe) is UnaryAffine and type(incoming) is int:
            return record.recipe.transfer.apply(incoming, self.ledger)
        if type(incoming) is RuntimeValueID:
            prior = values.resolve(incoming)
            if type(prior) is RuntimeTransferredState:
                previous = self.runtime_unary_record(prior.summary)
                if (previous.action, previous.side) != (record.action, record.side):
                    raise ValueError("nested summary input has another boundary sort")
                summary = self.combine_runtime_unary((prior.summary, summary))
                incoming = prior.incoming
        return values.transferred_state(summary, incoming)

    def context_value(
        self,
        summary: HigherSummaryID,
        left: RuntimeAtom,
        right: RuntimeAtom,
        incoming: RuntimeAtom,
        side: int,
    ) -> RuntimeAtom:
        self.runtime_context_record(summary)
        return self.semantics.runtime_values.context_state(
            summary,
            left,
            right,
            incoming,
            side,
        )

    def _intern(self, record: SummaryRecord) -> HigherSummaryID:
        found = self._keys.get(record)
        if found is not None:
            self.ledger.bump("higher_summary_semantic_hits")
            return self._handle(found, record)
        self.ledger.reserve_many(((self._node_owner, 1, 1), (self._key_owner, 1, 0)))
        local_id = len(self._nodes)
        self._nodes.append(record)
        self._keys[record] = local_id
        self.ledger.bump("higher_summary_semantic_publications")
        return self._handle(local_id, record)

    def _variable(
        self, action: FieldCellActionID, side: int, role: str
    ) -> HigherExpressionID:
        return self.semantics.variable(
            self.semantics.state_sort(action, side),
            f"higher-summary:{role}:{action.local_id}:{side}",
        )

    def apply_unary(
        self,
        summary: HigherSummaryID,
        state: HigherExpressionID,
    ) -> HigherExpressionID:
        record = self.unary_record(summary)
        if type(record) is not UnarySummary:
            raise ValueError("expression application received a runtime-only summary")
        if self.semantics.expression(state).sort != self.semantics.state_sort(
            record.action,
            record.side,
        ):
            raise ValueError("unary summary received another boundary sort")
        return self.semantics.apply(
            self.semantics.function_expression(record.function),
            state,
        )

    def apply_context(
        self,
        summary: HigherSummaryID,
        left: HigherExpressionID,
        right: HigherExpressionID,
        incoming: HigherExpressionID,
        side: int,
    ) -> HigherExpressionID:
        if type(side) is not int or side not in (0, 1):
            raise ValueError("context side must be zero or one")
        record = self.context_record(summary)
        if type(record) is not ContextSummary:
            raise ValueError("expression application received a runtime-only summary")
        body = record.left_body if side == 0 else record.right_body
        values = (
            (record.left, left),
            (record.right, right),
            (record.incoming_left if side == 0 else record.incoming_right, incoming),
        )
        for variable, replacement in values:
            body = self.semantics.bind_free(body, variable, replacement)
        return body

    def _make_unary(
        self,
        action: FieldCellActionID,
        side: int,
        variable: HigherExpressionID,
        body: HigherExpressionID,
        recipe: UnaryRecipe,
    ) -> HigherSummaryID:
        return self._intern(
            UnarySummary(
                action,
                side,
                self.semantics.function(variable, body),
                recipe,
            )
        )

    def _context_variables(
        self,
        provider: FieldCellActionID,
        consumer: FieldCellActionID,
    ) -> tuple[
        HigherExpressionID, HigherExpressionID, HigherExpressionID, HigherExpressionID
    ]:
        return (
            self._variable(provider, 0, f"context-left:{consumer.local_id}"),
            self._variable(provider, 1, f"context-right:{consumer.local_id}"),
            self._variable(consumer, 0, f"context-incoming-left:{provider.local_id}"),
            self._variable(consumer, 1, f"context-incoming-right:{provider.local_id}"),
        )

    def _make_context(
        self,
        provider: FieldCellActionID,
        consumer: FieldCellActionID,
        variables: tuple[
            HigherExpressionID,
            HigherExpressionID,
            HigherExpressionID,
            HigherExpressionID,
        ],
        left_body: HigherExpressionID,
        right_body: HigherExpressionID,
        recipe: ContextRecipe,
    ) -> HigherSummaryID:
        return self._intern(
            ContextSummary(
                provider,
                consumer,
                *variables,
                left_body,
                right_body,
                recipe,
            )
        )

    def _compose_unary_records(
        self,
        first: HigherSummaryID,
        second: HigherSummaryID,
    ) -> HigherSummaryID:
        before, after = self.unary_record(first), self.unary_record(second)
        if (before.action, before.side) != (after.action, after.side):
            raise ValueError("spatial unary summaries have incompatible interfaces")
        if type(before.recipe) is UnaryIdentity:
            self.ledger.bump("higher_identity_transfer_elisions")
            return second
        if type(after.recipe) is UnaryIdentity:
            self.ledger.bump("higher_identity_transfer_elisions")
            return first
        variable = self._variable(before.action, before.side, "spatial-unary")
        body = self.apply_unary(second, self.apply_unary(first, variable))
        return self._make_unary(
            before.action,
            before.side,
            variable,
            body,
            UnarySpatial(first, second),
        )

    def _compose_context_records(
        self,
        low: HigherSummaryID,
        high: HigherSummaryID,
        low_forward: HigherSummaryID,
        high_backward: HigherSummaryID,
    ) -> HigherSummaryID:
        low_record, high_record = self.context_record(low), self.context_record(high)
        if (low_record.provider, low_record.consumer) != (
            high_record.provider,
            high_record.consumer,
        ):
            raise ValueError("spatial contexts have incompatible interfaces")
        provider, consumer = low_record.provider, low_record.consumer
        variables = self._context_variables(provider, consumer)
        left, right, incoming_left, incoming_right = variables
        middle_left = self.apply_unary(low_forward, left)
        middle_right = self.apply_unary(high_backward, right)
        midpoint_left = self.apply_context(low, left, middle_right, incoming_left, 0)
        left_body = self.apply_context(high, middle_left, right, midpoint_left, 0)
        midpoint_right = self.apply_context(
            high,
            middle_left,
            right,
            incoming_right,
            1,
        )
        right_body = self.apply_context(low, left, middle_right, midpoint_right, 1)
        return self._make_context(
            provider,
            consumer,
            variables,
            left_body,
            right_body,
            ContextSpatial(low, high, low_forward, high_backward),
        )

    def unary(
        self,
        action: FieldCellActionID,
        source: SourceCellID,
        side: int,
    ) -> HigherSummaryID:
        self.schema.validate_action(action)
        self.sources.resolve(source)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("unary summary side must be zero or one")
        return self._ensure(_UnaryBinding(action, source, side))

    def context(
        self,
        provider: FieldCellActionID,
        consumer: FieldCellActionID,
        source: SourceCellID,
    ) -> HigherSummaryID:
        self.schema.validate_action(provider)
        self.schema.validate_action(consumer)
        self.sources.resolve(source)
        return self._ensure(_ContextBinding(provider, consumer, source))

    def _dependencies(
        self,
        key: _UnaryBinding | _ContextBinding,
    ) -> tuple[_UnaryBinding | _ContextBinding, ...]:
        node = self._input_geometry(key.source)
        if isinstance(key, _UnaryBinding):
            children = self.schema.children(key.action)
            if children is not None:
                before, after = children
                return (
                    _UnaryBinding(before, key.source, key.side),
                    _UnaryBinding(before, key.source, 1 - key.side),
                    _ContextBinding(before, after, key.source),
                )
            if node.level:
                low, high = self._input_children(key.source)
                first, second = (low, high) if key.side == 0 else (high, low)
                return (
                    _UnaryBinding(key.action, first, key.side),
                    _UnaryBinding(key.action, second, key.side),
                )
            return ()
        if node.level:
            low, high = self._input_children(key.source)
            return (
                _ContextBinding(key.provider, key.consumer, low),
                _ContextBinding(key.provider, key.consumer, high),
                _UnaryBinding(key.provider, low, 0),
                _UnaryBinding(key.provider, high, 1),
            )
        return ()

    def _blank_is_identity(self, action: FieldCellActionID, side: int) -> bool:
        from number_compiler.hashlife.execution.continuations.summary_dependencies import (
            _blank_is_identity,
        )

        return _blank_is_identity(self, action, side)

    def _runtime_dependencies(
        self,
        key: _UnaryBinding | _ContextBinding,
    ) -> tuple[_UnaryBinding | _ContextBinding, ...]:
        from number_compiler.hashlife.execution.continuations.summary_dependencies import (
            _runtime_dependencies,
        )

        return _runtime_dependencies(self, key)

    def _build(
        self,
        key: _UnaryBinding | _ContextBinding,
        dependencies: tuple[_UnaryBinding | _ContextBinding, ...],
    ) -> HigherSummaryID:
        node = self._input_geometry(key.source)
        if isinstance(key, _UnaryBinding):
            variable = self._variable(key.action, key.side, "unary")
            action_children = self.schema.children(key.action)
            if action_children is not None:
                before, _after = action_children
                forward, opposite, context = (
                    self._bindings[dependency] for dependency in dependencies
                )
                anchor = self.semantics.anchor(variable)
                continuation = self.semantics.continuation(variable)
                argument = self._variable(before, 1 - key.side, "unary-opposite")
                incoming = self.semantics.apply(
                    continuation,
                    self.apply_unary(opposite, argument),
                )
                left, right = (
                    (anchor, argument) if key.side == 0 else (argument, anchor)
                )
                continuation_body = self.apply_context(
                    context,
                    left,
                    right,
                    incoming,
                    key.side,
                )
                body = self.semantics.pair(
                    key.action,
                    key.side,
                    self.apply_unary(forward, anchor),
                    self.semantics.function(argument, continuation_body),
                )
                self.ledger.bump("higher_summary_temporal_compositions")
                return self._make_unary(
                    key.action,
                    key.side,
                    variable,
                    body,
                    UnaryTemporal(forward, opposite, context),
                )
            if node.level:
                self.ledger.bump("higher_summary_spatial_compositions")
                return self._compose_unary_records(
                    self._bindings[dependencies[0]],
                    self._bindings[dependencies[1]],
                )
            symbol = self.semantics.symbol(key.action, self._input_symbol(key.source))
            body = (
                variable
                if self.schema.kind(key.action) == "identity"
                else self.semantics.primitive_step(
                    key.action,
                    key.side,
                    variable,
                    symbol,
                )
            )
            return self._make_unary(
                key.action,
                key.side,
                variable,
                body,
                UnaryLeaf(self._input_symbol(key.source)),
            )
        if node.level:
            self.ledger.bump("higher_context_spatial_compositions")
            return self._compose_context_records(
                *(self._bindings[dependency] for dependency in dependencies),
            )
        variables = self._context_variables(key.provider, key.consumer)
        left, right, incoming_left, incoming_right = variables
        original = self.semantics.symbol(key.provider, self._input_symbol(key.source))
        symbol = self.semantics.action_emit(key.provider, left, original, right)
        left_body = self.semantics.action_step(key.consumer, 0, incoming_left, symbol)
        right_body = self.semantics.action_step(key.consumer, 1, incoming_right, symbol)
        return self._make_context(
            key.provider,
            key.consumer,
            variables,
            left_body,
            right_body,
            ContextLeaf(self._input_symbol(key.source)),
        )

    def _ensure(
        self,
        root: _UnaryBinding | _ContextBinding,
    ) -> HigherSummaryID:
        found = self._bindings.get(root)
        if found is not None:
            self.ledger.bump("higher_summary_binding_hits")
            return found
        stack: list[tuple[_UnaryBinding | _ContextBinding, bool]] = [(root, False)]
        active: set[_UnaryBinding | _ContextBinding] = set()
        while stack:
            key, ready = stack.pop()
            if key in self._bindings:
                active.discard(key)
                continue
            dependencies = self._dependencies(key)
            if not ready:
                if key in active:
                    raise AssertionError("cyclic higher summary dependency")
                active.add(key)
                stack.append((key, True))
                for dependency in reversed(dependencies):
                    if dependency not in self._bindings:
                        stack.append((dependency, False))
                continue
            missing = [item for item in dependencies if item not in self._bindings]
            if missing:
                stack.append((key, True))
                stack.extend((item, False) for item in reversed(missing))
                continue
            self.ledger.reserve(self._binding_owner, entries=1)
            try:
                result = self._build(key, dependencies)
                self._bindings[key] = result
            except BaseException:
                self.ledger.release(self._binding_owner, entries=1)
                raise
            active.discard(key)
        return self._bindings[root]

    def _build_runtime(
        self,
        key: _UnaryBinding | _ContextBinding,
        dependencies: tuple[_UnaryBinding | _ContextBinding, ...],
    ) -> HigherSummaryID:
        from number_compiler.hashlife.execution.continuations.summary_dependencies import (
            _build_runtime,
        )

        return _build_runtime(self, key, dependencies)

    def _ensure_runtime(
        self,
        root: _UnaryBinding | _ContextBinding,
    ) -> HigherSummaryID:
        from number_compiler.hashlife.execution.continuations.summary_dependencies import (
            _ensure_runtime,
        )

        return _ensure_runtime(self, root)

    def runtime_unary(
        self,
        action: FieldCellActionID,
        source: RuntimeInputCellID,
        side: int,
    ) -> HigherSummaryID:
        self.schema.validate_action(action)
        self.validate_input(source)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("runtime unary summary side must be zero or one")
        return self._ensure_runtime(_UnaryBinding(action, source, side))

    def runtime_context(
        self,
        provider: FieldCellActionID,
        consumer: FieldCellActionID,
        source: RuntimeInputCellID,
    ) -> HigherSummaryID:
        """Return one output-complete runtime U summary for a source cell."""
        self.schema.validate_action(provider)
        self.schema.validate_action(consumer)
        self.validate_input(source)
        return self._ensure_runtime(_ContextBinding(provider, consumer, source))

    def combine_runtime_unary(
        self,
        summaries: tuple[HigherSummaryID, ...],
    ) -> HigherSummaryID:
        if not summaries:
            raise ValueError("cannot combine an empty runtime unary range")
        from number_compiler.hashlife.execution.continuations.higher_runtime_composition import (
            compose_runtime_pair,
        )

        records = tuple(self.runtime_unary_record(item) for item in summaries)
        if any(
            (item.action, item.side) != (records[0].action, records[0].side)
            for item in records
        ):
            raise ValueError("runtime spatial summaries have incompatible interfaces")
        result = summaries[0]
        for following in summaries[1:]:
            result = compose_runtime_pair(self, result, following)
        return result

    def combine_unary(self, summaries: tuple[HigherSummaryID, ...]) -> HigherSummaryID:
        if not summaries:
            raise ValueError("cannot combine an empty unary range")
        result = summaries[0]
        for summary in summaries[1:]:
            result = self._compose_unary_records(result, summary)
        return result

    def combine_context(
        self,
        contexts: tuple[HigherSummaryID, ...],
        forward: tuple[HigherSummaryID, ...],
        backward: tuple[HigherSummaryID, ...],
    ) -> HigherSummaryID:
        if not contexts or not (len(contexts) == len(forward) == len(backward)):
            raise ValueError("context range components must be equally nonempty")
        result, result_forward, result_backward = contexts[0], forward[0], backward[0]
        for context, low_forward, high_backward in zip(
            contexts[1:],
            forward[1:],
            backward[1:],
            strict=True,
        ):
            result = self._compose_context_records(
                result,
                context,
                result_forward,
                high_backward,
            )
            result_forward = self._compose_unary_records(result_forward, low_forward)
            result_backward = self._compose_unary_records(
                high_backward, result_backward
            )
        return result


__all__ = [
    "ContextLeaf",
    "ContextSpatial",
    "ContextSummary",
    "HigherSummaryArena",
    "HigherSummaryID",
    "UnaryAffine",
    "UnaryFinite",
    "UnaryIdentity",
    "UnaryLeaf",
    "UnarySpatial",
    "UnarySummary",
    "UnaryTemporal",
]
