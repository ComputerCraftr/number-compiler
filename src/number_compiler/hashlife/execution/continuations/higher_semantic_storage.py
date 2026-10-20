"""Owner operations for retained higher expression and substitution state."""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from typing import Protocol

from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpression,
    HigherExpressionID,
    HigherRewriteKey,
)
from number_compiler.resources.ledger import ResourceLedger


class HigherSemanticStorage(Protocol):
    ledger: ResourceLedger
    _expressions: MutableSequence[HigherExpression]
    _expression_free_ids: MutableSequence[tuple[int, ...]]
    _rewrites: MutableMapping[HigherRewriteKey, HigherExpressionID]
    _rewrite_owner: int
    _substitutions: int
    _evaluations: int
    _evaluation_workspace_peak: int

    def expression_at(self, identity: int) -> HigherExpression:
        return self._expressions[identity]

    def free_variable_ids_at(self, identity: int) -> tuple[int, ...]:
        return self._expression_free_ids[identity]

    def begin_rewrite(self, key: HigherRewriteKey) -> HigherExpressionID | None:
        found = self._rewrites.get(key)
        if found is None:
            self.ledger.reserve(self._rewrite_owner, entries=1, nodes=0)
        return found

    def cancel_rewrite(self) -> None:
        self.ledger.release(self._rewrite_owner, entries=1)

    def publish_rewrite(
        self, key: HigherRewriteKey, result: HigherExpressionID
    ) -> None:
        self._rewrites[key] = result
        self._substitutions += 1

    def record_evaluation(self, peak: int) -> None:
        self._evaluations += 1
        self._evaluation_workspace_peak = max(self._evaluation_workspace_peak, peak)
