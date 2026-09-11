import pytest

from devtools.proofs import exact_oracle
from devtools.proofs.reverse_consumer_residual_audit import (
    audit_reverse_consumer_residuals,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded


def test_complete_small_mod9_interface_collapses_branch_hidden_consumers() -> None:
    with exact_oracle():
        rows = tuple(
            audit_reverse_consumer_residuals(capacity) for capacity in range(1, 5)
        )
    assert tuple(row.context_rows for row in rows) == (10, 29, 219, 580)
    for row in rows:
        assert row.action_admitted_rows + row.overflow_rows == row.context_rows
        assert row.exact_response_classes <= row.structural_consumer_occurrences
        assert row.branch_masked_occurrences > 0
        assert row.scan_work == row.context_rows * row.reachable_nodes
        assert (
            row.initial_action_classes
            <= row.horizon_1_classes
            <= row.horizon_2_classes
            <= row.horizon_4_classes
            <= row.pullback_classes
        )
        assert not row.initial_successor_closed
        assert row.refined_successor_conflicts == 0
        assert row.refined_successor_closed
        assert not row.general_successor_closure_claimed


def test_consumer_residual_audit_fails_before_response_allocation() -> None:
    with exact_oracle():
        with pytest.raises(BlockContextBudgetExceeded, match="context budget"):
            audit_reverse_consumer_residuals(4, max_contexts=579)
        with pytest.raises(BlockContextBudgetExceeded, match="cell budget"):
            audit_reverse_consumer_residuals(4, max_cells=1)
