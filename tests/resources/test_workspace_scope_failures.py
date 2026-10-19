"""Resource scopes cover setup, mutation failure, and caller mode restoration."""

from contextlib import closing
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.branch_quotients import PrimeBucketWorkspace
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.resources.closed_interface_workspace import (
    ClosedInterfaceWorkspace,
)
from number_compiler.resources.fused_traversal_workspace import FusedTraversalWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
)
from number_compiler.sequences.prime.select import PrimePrefixRank


@pytest.mark.parametrize("fused", (False, True))
def test_workspace_setup_failure_releases_reservations(
    fused: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    workspace = (
        FusedTraversalWorkspace(ledger, "setup")
        if fused
        else ClosedInterfaceWorkspace(ledger, "setup")
    )

    def fail_bookkeeping(_name: str, _amount: int = 1) -> Never:
        raise RuntimeError("setup bookkeeping failed")

    with monkeypatch.context() as patch:
        patch.setattr(ledger, "bump", fail_bookkeeping)
        with (
            pytest.raises(RuntimeError, match="setup bookkeeping failed"),
            (
                workspace.scope(1, 2)
                if isinstance(workspace, FusedTraversalWorkspace)
                else workspace.scope("leaf")
            ),
        ):
            pytest.fail("setup should fail before yielding")
    assert ledger.nodes == ledger.entries == workspace.nodes == 0
    with (
        workspace.scope(1, 2)
        if isinstance(workspace, FusedTraversalWorkspace)
        else workspace.scope("leaf")
    ):
        assert workspace.nodes > 0
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize("mutated", (False, True))
@pytest.mark.parametrize("fail_on", (1, 2))
def test_dyadic_stack_append_failure_rolls_back_its_reservation(
    mutated: bool, fail_on: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    workspace = DyadicReturnImageWorkspace(ledger, 0, 0, ANTIHYDRA_ARITHMETIC_LAW)
    stack = workspace.construction_stack
    original = LedgerList.append
    calls = 0

    def fail_append(self: LedgerList[object], value: object) -> None:
        nonlocal calls
        if self is stack:
            calls += 1
            if calls == fail_on:
                if mutated:
                    original(self, value)
                raise MemoryError("stack append failed")
        original(self, value)

    before = ledger.entries, ledger.nodes
    with monkeypatch.context() as patch:
        patch.setattr(LedgerList, "append", fail_append)
        with pytest.raises(MemoryError, match="stack append failed"):
            workspace.action_for_extent(256)
    assert (ledger.entries, ledger.nodes) == before
    assert len(stack) == 0
    workspace.action_for_extent(256)
    workspace.dispose()
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("fail", (False, True))
def test_prime_discovery_restores_already_suspended_publication(
    fail: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    with closing(
        PrimePrefixRank(max_states=10_000, max_work=100_000, max_stages=100)
    ) as owner:
        owner.dag.shared_publication_enabled = False

        def failed_rank(_bound: int) -> Never:
            raise RuntimeError("discovery failed")

        if fail:
            monkeypatch.setattr(owner.dag, "count", failed_rank)
            with pytest.raises(RuntimeError, match="discovery failed"):
                owner.cover(100)
        else:
            owner.cover(100)
        assert owner.dag.shared_publication_enabled is False


def test_prime_bucket_cleanup_retires_scratch_owner() -> None:
    ledger = ResourceLedger()
    with closing(PrimeBucketWorkspace(ledger)) as workspace:
        workspace.partition("mahler", 5)
    assert ledger.entries == ledger.nodes == 0
    assert all(row.disposed for row in ledger.inventory())


def test_nested_reservations_preserve_outer_capacity_and_reusable_owner() -> None:
    ledger = ResourceLedger(max_nodes=5)
    owner = ledger.register("scratch", "temporary")
    with ledger.reservation(owner, nodes=2):
        with (
            pytest.raises(ValueError, match="body failed"),
            ledger.reservation(owner, nodes=3),
        ):
            assert ledger.nodes == 5
            raise ValueError("body failed")
        assert ledger.nodes == 2
        with (
            pytest.raises(BlockContextBudgetExceeded),
            ledger.reservation(owner, nodes=4),
        ):
            pytest.fail("budget refusal must not enter body")
        assert ledger.nodes == 2
    assert ledger.nodes == ledger.entries == 0
    with ledger.reservation(owner, nodes=5):
        assert ledger.nodes == 5
    assert ledger.nodes == 0
