"""Canonical K/U summaries for recursively composed field actions.

The records in this module are source independent semantic functions.  Exact
source cells occur only in the evictable binding maps used while compiling a
summary.  K and U are built iteratively and contain expression/function IDs,
never source digits, future words, or proof-machine states.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_summary_records import (
    ContextBinding,
    ContextLeaf,
    ContextRecipe,
    ContextSpatial,
    ContextSummary,
    HigherSummaryID,
    RuntimeContextSummary,
    RuntimeUnarySummary,
    SummaryRecord,
    UnaryAffine,
    UnaryBinding,
    UnaryFinite,
    UnaryIdentity,
    UnaryLeaf,
    UnaryRecipe,
    UnarySpatial,
    UnarySummary,
    UnaryTemporal,
)
from number_compiler.hashlife.execution.continuations.higher_summary_snapshot import (
    HigherSummaryAuditSnapshot,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
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
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.stores import LedgerDict, LedgerList, append_indexed_node


@dataclass(frozen=True, slots=True)
class InputCellGeometry:
    """Read-only geometry of the authenticated source cell."""

    level: int
    uniform_symbol: int | None


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
        self._runtime_compositions: LedgerDict[
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
        self._nodes: LedgerList[SummaryRecord] = self.ledger.make_list(self._node_owner)
        self._keys: LedgerDict[SummaryRecord, int] = self.ledger.make_dict(
            self._key_owner
        )
        self._bindings: LedgerDict[UnaryBinding | ContextBinding, HigherSummaryID] = (
            self.ledger.make_dict(self._binding_owner)
        )
        self._runtime_bindings: LedgerDict[
            UnaryBinding | ContextBinding, HigherSummaryID
        ] = self.ledger.make_dict(self._runtime_binding_owner)
        self._blank_identity: LedgerDict[tuple[FieldCellActionID, int], bool] = (
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

    def audit_snapshot(self) -> HigherSummaryAuditSnapshot:
        """Expose the exact stores and read-only views for explicit audits."""
        return HigherSummaryAuditSnapshot(
            self.ledger,
            self.owner,
            self.semantics,
            self.sources,
            self.schema,
            self._node_owner,
            self._nodes,
            self._nodes.audit_view(),
            self._key_owner,
            self._keys,
            self._keys.audit_view(),
            self._binding_owner,
            self._bindings,
            self._bindings.audit_view(),
            self._runtime_binding_owner,
            self._runtime_bindings,
            self._runtime_bindings.audit_view(),
            self._blank_identity_owner,
            self._blank_identity,
            self._blank_identity.audit_view(),
            self._runtime_composition_owner,
            self._runtime_compositions,
            self._runtime_compositions.audit_view(),
        )

    def validate_input(self, cell: SourceCellID) -> None:
        if type(cell) is not SourceCellID:
            raise TypeError("summary input requires an issued source cell")
        self.sources.resolve(cell)

    def input_geometry(self, cell: SourceCellID) -> InputCellGeometry:
        self.validate_input(cell)
        node = self.sources.resolve(cell)
        return InputCellGeometry(node.level, node.uniform_symbol)

    def _input_children(self, cell: SourceCellID) -> tuple[SourceCellID, SourceCellID]:
        self.validate_input(cell)
        return self.sources.children(cell)

    def input_symbol(self, cell: SourceCellID) -> int:
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

    def scoped_handle(self, local_id: int, record: SummaryRecord) -> HigherSummaryID:
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
            self.ledger.bump(_execution_keys.HIGHER_IDENTITY_TRANSFER_ELISIONS)
            return incoming
        if type(record.recipe) is UnaryFinite and type(incoming) is int:
            self.ledger.bump(_execution_keys.HIGHER_FINITE_TRANSFER_STATE_VISITS)
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

    def intern_summary(self, record: SummaryRecord) -> HigherSummaryID:
        found = self._keys.get(record)
        if found is not None:
            self.ledger.bump(_execution_keys.HIGHER_SUMMARY_SEMANTIC_HITS)
            return self.scoped_handle(found, record)
        local_id = append_indexed_node(
            self.ledger,
            self._nodes,
            self._keys,
            self._node_owner,
            self._key_owner,
            record,
            record,
        )
        self.ledger.bump(_execution_keys.HIGHER_SUMMARY_SEMANTIC_PUBLICATIONS)
        return self.scoped_handle(local_id, record)

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
        return self.intern_summary(
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
        return self.intern_summary(
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
            self.ledger.bump(_execution_keys.HIGHER_IDENTITY_TRANSFER_ELISIONS)
            return second
        if type(after.recipe) is UnaryIdentity:
            self.ledger.bump(_execution_keys.HIGHER_IDENTITY_TRANSFER_ELISIONS)
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
        return self._ensure(UnaryBinding(action, source, side))

    def context(
        self,
        provider: FieldCellActionID,
        consumer: FieldCellActionID,
        source: SourceCellID,
    ) -> HigherSummaryID:
        self.schema.validate_action(provider)
        self.schema.validate_action(consumer)
        self.sources.resolve(source)
        return self._ensure(ContextBinding(provider, consumer, source))

    def summary_dependencies(
        self,
        key: UnaryBinding | ContextBinding,
    ) -> tuple[UnaryBinding | ContextBinding, ...]:
        node = self.input_geometry(key.source)
        if isinstance(key, UnaryBinding):
            children = self.schema.children(key.action)
            if children is not None:
                before, after = children
                return (
                    UnaryBinding(before, key.source, key.side),
                    UnaryBinding(before, key.source, 1 - key.side),
                    ContextBinding(before, after, key.source),
                )
            if node.level:
                low, high = self._input_children(key.source)
                first, second = (low, high) if key.side == 0 else (high, low)
                return (
                    UnaryBinding(key.action, first, key.side),
                    UnaryBinding(key.action, second, key.side),
                )
            return ()
        if node.level:
            low, high = self._input_children(key.source)
            return (
                ContextBinding(key.provider, key.consumer, low),
                ContextBinding(key.provider, key.consumer, high),
                UnaryBinding(key.provider, low, 0),
                UnaryBinding(key.provider, high, 1),
            )
        return ()

    def blank_is_identity(self, action: FieldCellActionID, side: int) -> bool:
        from number_compiler.hashlife.execution.continuations.summary_dependencies import (
            blank_is_identity,
        )

        return blank_is_identity(self, action, side)

    def runtime_dependencies(
        self,
        key: UnaryBinding | ContextBinding,
    ) -> tuple[UnaryBinding | ContextBinding, ...]:
        from number_compiler.hashlife.execution.continuations.summary_dependencies import (
            runtime_dependencies,
        )

        return runtime_dependencies(self, key)

    def _build(
        self,
        key: UnaryBinding | ContextBinding,
        dependencies: tuple[UnaryBinding | ContextBinding, ...],
    ) -> HigherSummaryID:
        node = self.input_geometry(key.source)
        if isinstance(key, UnaryBinding):
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
                self.ledger.bump(_execution_keys.HIGHER_SUMMARY_TEMPORAL_COMPOSITIONS)
                return self._make_unary(
                    key.action,
                    key.side,
                    variable,
                    body,
                    UnaryTemporal(forward, opposite, context),
                )
            if node.level:
                self.ledger.bump(_execution_keys.HIGHER_SUMMARY_SPATIAL_COMPOSITIONS)
                return self._compose_unary_records(
                    self._bindings[dependencies[0]],
                    self._bindings[dependencies[1]],
                )
            symbol = self.semantics.symbol(key.action, self.input_symbol(key.source))
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
                UnaryLeaf(self.input_symbol(key.source)),
            )
        if node.level:
            self.ledger.bump(_execution_keys.HIGHER_CONTEXT_SPATIAL_COMPOSITIONS)
            return self._compose_context_records(
                *(self._bindings[dependency] for dependency in dependencies),
            )
        variables = self._context_variables(key.provider, key.consumer)
        left, right, incoming_left, incoming_right = variables
        original = self.semantics.symbol(key.provider, self.input_symbol(key.source))
        symbol = self.semantics.action_emit(key.provider, left, original, right)
        left_body = self.semantics.action_step(key.consumer, 0, incoming_left, symbol)
        right_body = self.semantics.action_step(key.consumer, 1, incoming_right, symbol)
        return self._make_context(
            key.provider,
            key.consumer,
            variables,
            left_body,
            right_body,
            ContextLeaf(self.input_symbol(key.source)),
        )

    def _ensure(
        self,
        root: UnaryBinding | ContextBinding,
    ) -> HigherSummaryID:
        found = self._bindings.get(root)
        if found is not None:
            self.ledger.bump(_execution_keys.HIGHER_SUMMARY_BINDING_HITS)
            return found
        stack: list[tuple[UnaryBinding | ContextBinding, bool]] = [(root, False)]
        active: set[UnaryBinding | ContextBinding] = set()
        while stack:
            key, ready = stack.pop()
            if key in self._bindings:
                active.discard(key)
                continue
            dependencies = self.summary_dependencies(key)
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

    def build_runtime(
        self,
        key: UnaryBinding | ContextBinding,
        dependencies: tuple[UnaryBinding | ContextBinding, ...],
    ) -> HigherSummaryID:
        from number_compiler.hashlife.execution.continuations.summary_dependencies import (
            build_runtime,
        )

        return build_runtime(self, key, dependencies)

    def ensure_runtime(
        self,
        root: UnaryBinding | ContextBinding,
    ) -> HigherSummaryID:
        from number_compiler.hashlife.execution.continuations.summary_dependencies import (
            ensure_runtime,
        )

        return ensure_runtime(self, root)

    def publish_runtime_composition(
        self,
        key: tuple[HigherSummaryID, HigherSummaryID],
        record: RuntimeUnarySummary,
        *,
        context: RuntimeContextSummary | None = None,
    ) -> HigherSummaryID:
        """Reserve the complete parent, its context, and its binding together."""
        found = self._keys.get(record)
        context_new = context is not None and context not in self._keys
        charges = [(self._runtime_composition_owner, 1, 0)]
        if found is None:
            charges.extend(((self._node_owner, 1, 1), (self._key_owner, 1, 0)))
        if context_new:
            charges.extend(((self._node_owner, 1, 1), (self._key_owner, 1, 0)))
        self.ledger.reserve_many(charges)
        if context_new:
            assert context is not None
            local_id = len(self._nodes)
            self._nodes.append(context)
            self._keys[context] = local_id
            self.ledger.bump(_execution_keys.HIGHER_SUMMARY_SEMANTIC_PUBLICATIONS)
        elif context is not None:
            self.ledger.bump(_execution_keys.HIGHER_SUMMARY_SEMANTIC_HITS)
        if found is None:
            found = len(self._nodes)
            self._nodes.append(record)
            self._keys[record] = found
            self.ledger.bump(_execution_keys.HIGHER_SUMMARY_SEMANTIC_PUBLICATIONS)
        else:
            self.ledger.bump(_execution_keys.HIGHER_SUMMARY_SEMANTIC_HITS)
        result = self.scoped_handle(found, record)
        self._runtime_compositions[key] = result
        return result

    @property
    def runtime_bindings(
        self,
    ) -> Mapping[UnaryBinding | ContextBinding, HigherSummaryID]:
        return self._runtime_bindings.audit_view()

    @property
    def runtime_compositions(
        self,
    ) -> Mapping[tuple[HigherSummaryID, HigherSummaryID], HigherSummaryID]:
        return self._runtime_compositions.audit_view()

    @property
    def blank_identities(self) -> Mapping[tuple[FieldCellActionID, int], bool]:
        return self._blank_identity.audit_view()

    def publish_blank_identity(
        self, key: tuple[FieldCellActionID, int], value: bool
    ) -> None:
        self.ledger.reserve(self._blank_identity_owner, entries=1)
        self._blank_identity[key] = value

    def build_and_bind_runtime(
        self,
        key: UnaryBinding | ContextBinding,
        dependencies: tuple[UnaryBinding | ContextBinding, ...],
    ) -> None:
        self.ledger.reserve(self._runtime_binding_owner, entries=1)
        try:
            result = self.build_runtime(key, dependencies)
            self._runtime_bindings[key] = result
        except BaseException:
            self.ledger.release(self._runtime_binding_owner, entries=1)
            raise
        self.ledger.bump(_execution_keys.HIGHER_RUNTIME_SUMMARY_PUBLICATIONS)

    def prospective_summary(self, record: SummaryRecord) -> HigherSummaryID:
        return self.scoped_handle(self._keys.get(record, len(self._nodes)), record)

    def runtime_unary(
        self,
        action: FieldCellActionID,
        source: SourceCellID,
        side: int,
    ) -> HigherSummaryID:
        self.schema.validate_action(action)
        self.validate_input(source)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("runtime unary summary side must be zero or one")
        return self.ensure_runtime(UnaryBinding(action, source, side))

    def runtime_context(
        self,
        provider: FieldCellActionID,
        consumer: FieldCellActionID,
        source: SourceCellID,
    ) -> HigherSummaryID:
        """Return one output-complete runtime U summary for a source cell."""
        self.schema.validate_action(provider)
        self.schema.validate_action(consumer)
        self.validate_input(source)
        return self.ensure_runtime(ContextBinding(provider, consumer, source))

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
    "ContextBinding",
    "ContextLeaf",
    "ContextRecipe",
    "ContextSpatial",
    "ContextSummary",
    "HigherSummaryArena",
    "HigherSummaryID",
    "RuntimeContextSummary",
    "RuntimeUnarySummary",
    "SummaryRecord",
    "UnaryAffine",
    "UnaryBinding",
    "UnaryFinite",
    "UnaryIdentity",
    "UnaryLeaf",
    "UnaryRecipe",
    "UnarySpatial",
    "UnarySummary",
    "UnaryTemporal",
]
