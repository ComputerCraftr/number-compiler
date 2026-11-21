"""Check stationary five-power column signals against literal arithmetic."""

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.carry.five_power_column import five_power_column_word
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("column", range(6))
def test_stationary_column_matches_independent_powers(column: int) -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("column-scratch", "workspace")
    arena = LedgerSLPArena(ledger, "column", "arithmetic")
    try:
        start = column + 3
        root = five_power_column_word(
            arena, ledger, scratch, column=column, exponent=start, samples=53
        )
        expected = tuple((5**n // 10**column) % 10 for n in range(start, start + 53))
        assert arena.materialize(root) == expected
        assert ledger.account_usage(scratch) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(scratch)
    assert ledger.nodes == ledger.entries == 0


def test_column_rejects_unsettled_exponent_without_allocating() -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("column-invalid", "workspace")
    arena = LedgerSLPArena(ledger, "column-invalid", "arithmetic")
    try:
        nodes = len(arena.nodes)
        with pytest.raises(ValueError, match="stationary"):
            five_power_column_word(
                arena, ledger, scratch, column=3, exponent=3, samples=10
            )
        assert len(arena.nodes) == nodes
    finally:
        arena.dispose()
        ledger.mark_disposed(scratch)


def test_stationary_column_pumps_large_horizon_without_expansion() -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("column-large-scratch", "workspace")
    arena = LedgerSLPArena(ledger, "column-large", "arithmetic")
    try:
        count = 10**18 + 3
        root = five_power_column_word(
            arena, ledger, scratch, column=2, exponent=5, samples=count
        )
        assert arena.nodes[root].length == count
        last = pow(5, 5 + count - 1, 1000) // 100
        assert symbol_at(arena, root, count - 1) == last
        assert len(arena.nodes) < 30
    finally:
        arena.dispose()
        ledger.mark_disposed(scratch)
