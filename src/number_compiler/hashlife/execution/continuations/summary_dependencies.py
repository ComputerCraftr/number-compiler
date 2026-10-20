"""Store-free summary dependencies operations."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.radix_transfer import RadixRemainderTransfer
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        ContextBinding,
        HigherSummaryArena,
        HigherSummaryID,
        UnaryBinding,
    )


def runtime_dependencies(
    self: HigherSummaryArena,
    key: UnaryBinding | ContextBinding,
) -> tuple[UnaryBinding | ContextBinding, ...]:
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        UnaryBinding,
    )

    if isinstance(key, UnaryBinding):
        node = self.input_geometry(key.source)
        _base, blank = self.schema.alphabet(key.action)
        if node.uniform_symbol == blank and self.blank_is_identity(
            key.action, key.side
        ):
            return ()
    return self.summary_dependencies(key)


def build_runtime(
    self: HigherSummaryArena,
    key: UnaryBinding | ContextBinding,
    dependencies: tuple[UnaryBinding | ContextBinding, ...],
) -> HigherSummaryID:
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        ContextLeaf,
        ContextSpatial,
        RuntimeContextSummary,
        RuntimeUnarySummary,
        UnaryAffine,
        UnaryBinding,
        UnaryFinite,
        UnaryIdentity,
        UnaryLeaf,
        UnaryRecipe,
        UnaryTemporal,
    )

    node = self.input_geometry(key.source)
    resolved = tuple(self.runtime_bindings[item] for item in dependencies)
    if isinstance(key, UnaryBinding):
        if self.schema.kind(key.action) == "identity":
            return self.intern_summary(
                RuntimeUnarySummary(
                    key.action,
                    key.side,
                    UnaryIdentity(),
                )
            )
        _base, blank = self.schema.alphabet(key.action)
        if node.uniform_symbol == blank and self.blank_is_identity(
            key.action, key.side
        ):
            return self.intern_summary(
                RuntimeUnarySummary(
                    key.action,
                    key.side,
                    UnaryIdentity(),
                )
            )
        if self.schema.children(key.action) is not None:
            return self.intern_summary(
                RuntimeUnarySummary(
                    key.action,
                    key.side,
                    UnaryTemporal(resolved[0], resolved[1], resolved[2]),
                )
            )
        if node.level:
            return self.combine_runtime_unary((resolved[0], resolved[1]))
        cardinality = self.schema.state_count(key.action, key.side)
        leaf_hook = getattr(self.schema, "runtime_unary_leaf", None)
        affine = (
            cast(
                Callable[[FieldCellActionID, int, int], RadixRemainderTransfer | None],
                leaf_hook,
            )(key.action, key.side, self.input_symbol(key.source))
            if leaf_hook is not None
            else None
        )
        if affine is not None:
            if (
                type(affine) is not RadixRemainderTransfer
                or affine.radix != cardinality
            ):
                raise ValueError("symbolic primitive transfer has another port sort")
            affine.__post_init__()
            return self.intern_summary(
                RuntimeUnarySummary(key.action, key.side, UnaryAffine(affine))
            )
        if cardinality <= 64:
            symbol = self.input_symbol(key.source)
            outputs = tuple(
                self.semantics.primitive_tables.step(
                    key.action,
                    key.side,
                    state,
                    symbol,
                )
                for state in range(cardinality)
            )
            self.ledger.bump(_execution_keys.HIGHER_FINITE_TRANSFER_EVALUATIONS)
            self.ledger.bump(
                _execution_keys.HIGHER_FINITE_TRANSFER_STATE_VISITS,
                cardinality,
            )
            recipe: UnaryRecipe = (
                UnaryIdentity()
                if outputs == tuple(range(cardinality))
                else UnaryFinite(outputs)
            )
            return self.intern_summary(
                RuntimeUnarySummary(key.action, key.side, recipe)
            )
        return self.intern_summary(
            RuntimeUnarySummary(
                key.action,
                key.side,
                UnaryLeaf(self.input_symbol(key.source)),
            )
        )
    if node.level:
        return self.intern_summary(
            RuntimeContextSummary(
                key.provider,
                key.consumer,
                ContextSpatial(resolved[0], resolved[1], resolved[2], resolved[3]),
            )
        )
    return self.intern_summary(
        RuntimeContextSummary(
            key.provider,
            key.consumer,
            ContextLeaf(self.input_symbol(key.source)),
        )
    )


def ensure_runtime(
    self: HigherSummaryArena,
    root: UnaryBinding | ContextBinding,
) -> HigherSummaryID:

    found = self.runtime_bindings.get(root)
    if found is not None:
        self.ledger.bump(_execution_keys.HIGHER_RUNTIME_SUMMARY_BINDING_HITS)
        return found
    stack: list[tuple[UnaryBinding | ContextBinding, bool]] = [(root, False)]
    active: set[UnaryBinding | ContextBinding] = set()
    while stack:
        key, ready = stack.pop()
        if key in self.runtime_bindings:
            active.discard(key)
            continue
        dependencies = self.runtime_dependencies(key)
        if not ready:
            if key in active:
                raise AssertionError("cyclic runtime summary dependency")
            active.add(key)
            stack.append((key, True))
            for dependency in reversed(dependencies):
                if dependency not in self.runtime_bindings:
                    stack.append((dependency, False))
            continue
        missing = [item for item in dependencies if item not in self.runtime_bindings]
        if missing:
            stack.append((key, True))
            stack.extend((item, False) for item in reversed(missing))
            continue
        self.build_and_bind_runtime(key, dependencies)
        active.discard(key)
    return self.runtime_bindings[root]


def blank_is_identity(
    self: HigherSummaryArena, action: FieldCellActionID, side: int
) -> bool:
    root = action, side
    cached = self.blank_identities.get(root)
    if cached is not None:
        return cached
    stack: list[tuple[FieldCellActionID, bool]] = [(action, False)]
    while stack:
        current, ready = stack.pop()
        key = current, side
        if key in self.blank_identities:
            continue
        children = self.schema.children(current)
        if children is not None:
            if not ready:
                stack.append((current, True))
                stack.extend((child, False) for child in children)
                continue
            result = all(self.blank_identities[child, side] for child in children)
            self.publish_blank_identity(key, result)
            continue
        blank_hook = getattr(self.schema, "runtime_blank_identity", None)
        certified = (
            cast(Callable[[FieldCellActionID, int], bool | None], blank_hook)(
                current, side
            )
            if blank_hook is not None
            else None
        )
        if certified is not None:
            if type(certified) is not bool:
                raise TypeError("blank identity certificate must be Boolean")
            self.publish_blank_identity(key, certified)
            continue
        _base, blank = self.schema.alphabet(current)
        state_count = self.schema.state_count(current, side)
        opposite_count = self.schema.state_count(current, 1 - side)
        step_identity = all(
            self.schema.step(current, side, state, blank) == state
            for state in range(state_count)
        )
        emits_blank = all(
            self.schema.emit(current, left, blank, right) == blank
            for left in range(state_count if side == 0 else opposite_count)
            for right in range(opposite_count if side == 0 else state_count)
        )
        self.publish_blank_identity(key, step_identity and emits_blank)
    return self.blank_identities[root]
