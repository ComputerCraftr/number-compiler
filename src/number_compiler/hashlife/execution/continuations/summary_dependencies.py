"""Store-free summary dependencies operations."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.radix_transfer import RadixRemainderTransfer
from number_compiler.hashlife.actions.field_actions import FieldCellActionID

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        HigherSummaryArena,
        HigherSummaryID,
        _ContextBinding,
        _UnaryBinding,
    )


def _runtime_dependencies(
    self: HigherSummaryArena,
    key: _UnaryBinding | _ContextBinding,
) -> tuple[_UnaryBinding | _ContextBinding, ...]:
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        _UnaryBinding,
    )

    if isinstance(key, _UnaryBinding):
        node = self._input_geometry(key.source)
        _base, blank = self.schema.alphabet(key.action)
        if node.uniform_symbol == blank and self._blank_is_identity(
            key.action, key.side
        ):
            return ()
    return self._dependencies(key)


def _build_runtime(
    self: HigherSummaryArena,
    key: _UnaryBinding | _ContextBinding,
    dependencies: tuple[_UnaryBinding | _ContextBinding, ...],
) -> HigherSummaryID:
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        ContextLeaf,
        ContextSpatial,
        RuntimeContextSummary,
        RuntimeUnarySummary,
        UnaryAffine,
        UnaryFinite,
        UnaryIdentity,
        UnaryLeaf,
        UnaryRecipe,
        UnaryTemporal,
        _UnaryBinding,
    )

    node = self._input_geometry(key.source)
    resolved = tuple(self._runtime_bindings[item] for item in dependencies)
    if isinstance(key, _UnaryBinding):
        if self.schema.kind(key.action) == "identity":
            return self._intern(
                RuntimeUnarySummary(
                    key.action,
                    key.side,
                    UnaryIdentity(),
                )
            )
        _base, blank = self.schema.alphabet(key.action)
        if node.uniform_symbol == blank and self._blank_is_identity(
            key.action, key.side
        ):
            return self._intern(
                RuntimeUnarySummary(
                    key.action,
                    key.side,
                    UnaryIdentity(),
                )
            )
        if self.schema.children(key.action) is not None:
            return self._intern(
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
            )(key.action, key.side, self._input_symbol(key.source))
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
            return self._intern(
                RuntimeUnarySummary(key.action, key.side, UnaryAffine(affine))
            )
        if cardinality <= 64:
            symbol = self._input_symbol(key.source)
            outputs = tuple(
                self.semantics.primitive_tables.step(
                    key.action,
                    key.side,
                    state,
                    symbol,
                )
                for state in range(cardinality)
            )
            self.ledger.bump("higher_finite_transfer_evaluations")
            self.ledger.bump("higher_finite_transfer_state_visits", cardinality)
            recipe: UnaryRecipe = (
                UnaryIdentity()
                if outputs == tuple(range(cardinality))
                else UnaryFinite(outputs)
            )
            return self._intern(RuntimeUnarySummary(key.action, key.side, recipe))
        return self._intern(
            RuntimeUnarySummary(
                key.action,
                key.side,
                UnaryLeaf(self._input_symbol(key.source)),
            )
        )
    if node.level:
        return self._intern(
            RuntimeContextSummary(
                key.provider,
                key.consumer,
                ContextSpatial(resolved[0], resolved[1], resolved[2], resolved[3]),
            )
        )
    return self._intern(
        RuntimeContextSummary(
            key.provider,
            key.consumer,
            ContextLeaf(self._input_symbol(key.source)),
        )
    )


def _ensure_runtime(
    self: HigherSummaryArena,
    root: _UnaryBinding | _ContextBinding,
) -> HigherSummaryID:

    found = self._runtime_bindings.get(root)
    if found is not None:
        self.ledger.bump("higher_runtime_summary_binding_hits")
        return found
    stack: list[tuple[_UnaryBinding | _ContextBinding, bool]] = [(root, False)]
    active: set[_UnaryBinding | _ContextBinding] = set()
    while stack:
        key, ready = stack.pop()
        if key in self._runtime_bindings:
            active.discard(key)
            continue
        dependencies = self._runtime_dependencies(key)
        if not ready:
            if key in active:
                raise AssertionError("cyclic runtime summary dependency")
            active.add(key)
            stack.append((key, True))
            for dependency in reversed(dependencies):
                if dependency not in self._runtime_bindings:
                    stack.append((dependency, False))
            continue
        missing = [item for item in dependencies if item not in self._runtime_bindings]
        if missing:
            stack.append((key, True))
            stack.extend((item, False) for item in reversed(missing))
            continue
        self.ledger.reserve(self._runtime_binding_owner, entries=1)
        try:
            result = self._build_runtime(key, dependencies)
            self._runtime_bindings[key] = result
        except BaseException:
            self.ledger.release(self._runtime_binding_owner, entries=1)
            raise
        self.ledger.bump("higher_runtime_summary_publications")
        active.discard(key)
    return self._runtime_bindings[root]


def _blank_is_identity(
    self: HigherSummaryArena, action: FieldCellActionID, side: int
) -> bool:
    root = action, side
    cached = self._blank_identity.get(root)
    if cached is not None:
        return cached
    stack: list[tuple[FieldCellActionID, bool]] = [(action, False)]
    while stack:
        current, ready = stack.pop()
        key = current, side
        if key in self._blank_identity:
            continue
        children = self.schema.children(current)
        if children is not None:
            if not ready:
                stack.append((current, True))
                stack.extend((child, False) for child in children)
                continue
            result = all(self._blank_identity[child, side] for child in children)
            self.ledger.reserve(self._blank_identity_owner, entries=1)
            self._blank_identity[key] = result
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
            self.ledger.reserve(self._blank_identity_owner, entries=1)
            self._blank_identity[key] = certified
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
        self.ledger.reserve(self._blank_identity_owner, entries=1)
        self._blank_identity[key] = step_identity and emits_blank
    return self._blank_identity[root]
