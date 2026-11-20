"""Shared admission of a cached bounded decimal-reversal execution owner."""

from __future__ import annotations

from typing import TYPE_CHECKING, Protocol

if TYPE_CHECKING:
    from number_compiler.api.number_api import NumberCompiler
    from number_compiler.api.query_types import (
        DoubleReverseTermQuery,
        FiveReverseTermQuery,
    )
    from number_compiler.resources.ledger import ResourceLedger


class BoundedDecimalOwner(Protocol):
    @property
    def seed(self) -> int: ...
    @property
    def generation(self) -> int: ...
    @property
    def max_steps(self) -> int: ...
    @property
    def max_state_bits(self) -> int: ...
    @property
    def resource_ledger(self) -> ResourceLedger: ...
    @property
    def is_usable(self) -> bool: ...


def matches_bounded_query(
    owner: BoundedDecimalOwner,
    query: DoubleReverseTermQuery | FiveReverseTermQuery,
    compiler: NumberCompiler,
) -> bool:
    """Check occurrence and budget bindings after the cache checks owner type."""
    owner_values = (
        owner.seed,
        owner.generation,
        owner.max_steps,
        owner.max_state_bits,
    )
    query_values = (query.seed, query.index, query.max_steps, query.max_state_bits)
    if any(type(value) is not int for value in (*owner_values, *query_values)):
        return False
    return (
        owner_values == query_values
        and owner.resource_ledger.max_nodes == compiler.max_context_nodes
        and owner.resource_ledger.max_cache_entries == compiler.max_cache_entries
        and owner.is_usable
    )
