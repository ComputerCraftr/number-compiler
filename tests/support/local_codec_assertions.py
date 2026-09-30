"""Atomic local-action publication checks with complete store-size snapshots."""

from collections.abc import Callable, Sized

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger


def assert_publication_refused(
    ledger: ResourceLedger,
    stores: tuple[Sized, ...],
    operation: Callable[[], object],
) -> None:
    before_entries, before_nodes = ledger.entries, ledger.nodes
    before_sizes = tuple(map(len, stores))
    ledger.tighten_limits(before_nodes, before_entries)
    with pytest.raises(BlockContextBudgetExceeded):
        operation()
    assert (ledger.entries, ledger.nodes) == (before_entries, before_nodes)
    assert tuple(map(len, stores)) == before_sizes
