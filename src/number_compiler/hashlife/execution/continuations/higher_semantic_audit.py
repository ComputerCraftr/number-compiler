"""Read-only retained-store snapshot for higher semantic payload audits."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_types import (
        HigherExpression,
        HigherExpressionID,
        HigherFunction,
        HigherRewriteKey,
    )


@dataclass(frozen=True, slots=True)
class HigherSemanticAuditSnapshot:
    """Exact owner bindings plus immutable views of all canonical indexes."""

    ledger: ResourceLedger
    owner: ArenaToken
    expression_owner: int
    expressions: tuple[HigherExpression, ...]
    expression_store: object
    expression_key_owner: int
    expression_keys: Mapping[HigherExpression, int]
    expression_key_store: object
    expression_free_owner: int
    expression_free_ids: tuple[tuple[int, ...], ...]
    expression_free_store: object
    function_owner: int
    functions: tuple[HigherFunction, ...]
    function_store: object
    function_key_owner: int
    function_keys: Mapping[HigherFunction, int]
    function_key_store: object
    rewrite_owner: int
    rewrites: Mapping[HigherRewriteKey, HigherExpressionID]
    rewrite_store: object

    @classmethod
    def from_stores(
        cls,
        ledger: ResourceLedger,
        owner: ArenaToken,
        expressions: tuple[int, Sequence[HigherExpression]],
        expression_keys: tuple[int, Mapping[HigherExpression, int]],
        expression_free_ids: tuple[int, Sequence[tuple[int, ...]]],
        functions: tuple[int, Sequence[HigherFunction]],
        function_keys: tuple[int, Mapping[HigherFunction, int]],
        rewrites: tuple[int, Mapping[HigherRewriteKey, HigherExpressionID]],
    ) -> HigherSemanticAuditSnapshot:
        """Build a shallow snapshot while preserving every backing-store identity."""
        expression_owner, expression_store = expressions
        expression_key_owner, expression_key_store = expression_keys
        expression_free_owner, expression_free_store = expression_free_ids
        function_owner, function_store = functions
        function_key_owner, function_key_store = function_keys
        rewrite_owner, rewrite_store = rewrites
        return cls(
            ledger=ledger,
            owner=owner,
            expression_owner=expression_owner,
            expressions=tuple(expression_store),
            expression_store=expression_store,
            expression_key_owner=expression_key_owner,
            expression_keys=MappingProxyType(expression_key_store),
            expression_key_store=expression_key_store,
            expression_free_owner=expression_free_owner,
            expression_free_ids=tuple(expression_free_store),
            expression_free_store=expression_free_store,
            function_owner=function_owner,
            functions=tuple(function_store),
            function_store=function_store,
            function_key_owner=function_key_owner,
            function_keys=MappingProxyType(function_key_store),
            function_key_store=function_key_store,
            rewrite_owner=rewrite_owner,
            rewrites=MappingProxyType(rewrite_store),
            rewrite_store=rewrite_store,
        )
