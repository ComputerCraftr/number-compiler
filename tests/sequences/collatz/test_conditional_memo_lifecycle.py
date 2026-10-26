"""Temporary lookup workspaces belong to each conditional memo's lifecycle."""

from unittest.mock import patch

import pytest

from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.ledger_records import ResourceInventory
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_harmonic_ring import (
    PeriodicTail6305Ring,
)
from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
    CertifiedSchedulerCandidate,
    issue_conditional_scheduler_candidate,
)
from number_compiler.sequences.collatz.conditional_scheduler_memo import (
    ConditionalSchedulerMemo,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    SourceClosedPortAction,
)


def _candidate() -> CertifiedSchedulerCandidate:
    motif = (0, 1)
    residue, modulus = PeriodicTail6305Ring.guard_residue(motif, 64)
    residue += ((3 - residue) * pow(modulus, -1, 5) % 5) * modulus
    source = residue + 5 * modulus * (1 << 48)
    ticks = 64 * sum(index + 4 for index in motif)
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "conditional-memo-test")
    with scratch.scope():
        candidate = issue_conditional_scheduler_candidate(
            source,
            ticks,
            scratch=scratch,
            ledger=ledger,
            max_coefficient_bits=8192,
        )
    assert candidate is not None
    return candidate


def _lookup(
    memo: ConditionalSchedulerMemo, candidate: CertifiedSchedulerCandidate
) -> CertifiedSchedulerCandidate | None:
    return memo.lookup_port(
        candidate.source,
        candidate.return_count,
        0,
        8192,
        candidate.source.bit_length(),
    )


def _lookup_accounts(ledger: ResourceLedger) -> tuple[ResourceInventory, ...]:
    return tuple(
        row
        for row in ledger.inventory()
        if row.role == "conditional_cache_lookup_workspace"
    )


def test_lookup_workspace_is_reused_and_disposed_with_its_memo() -> None:
    candidate = _candidate()
    ledger = ResourceLedger()
    memo = ConditionalSchedulerMemo(ledger)
    memo.remember_port(candidate, demand=0, coefficient_budget=8192)
    assert _lookup(memo, candidate) is candidate

    accounts = _lookup_accounts(ledger)
    assert len(accounts) == 1
    assert not accounts[0].disposed
    owner_count = ledger.owner_count
    balances = (ledger.entries, ledger.nodes)

    assert _lookup(memo, candidate) is candidate
    assert ledger.owner_count == owner_count
    assert (ledger.entries, ledger.nodes) == balances
    assert len(_lookup_accounts(ledger)) == 1

    memo.close()
    assert all(row.disposed for row in _lookup_accounts(ledger))
    assert ledger.entries == ledger.nodes == 0
    memo.close()


def test_shared_ledger_memos_have_independent_lookup_workspaces() -> None:
    candidate = _candidate()
    ledger = ResourceLedger()
    first = ConditionalSchedulerMemo(ledger)
    second = ConditionalSchedulerMemo(ledger)
    first.remember_port(candidate, demand=0, coefficient_budget=8192)
    second.remember_port(candidate, demand=0, coefficient_budget=8192)

    assert _lookup(first, candidate) is candidate
    assert _lookup(second, candidate) is candidate
    accounts = _lookup_accounts(ledger)
    assert len(accounts) == 2
    assert len({row.owner for row in accounts}) == 2
    assert len({row.name for row in accounts}) == 2

    first.close()
    assert _lookup(second, candidate) is candidate
    second_owner = next(
        row for row in _lookup_accounts(ledger) if row.owner == accounts[1].owner
    )
    assert not second_owner.disposed
    second.close()
    assert ledger.entries == ledger.nodes == 0


def test_budget_bypass_closes_lookup_reservation_and_keeps_memo_usable() -> None:
    candidate = _candidate()
    ledger = ResourceLedger()
    memo = ConditionalSchedulerMemo(ledger)
    memo.remember_port(candidate, demand=0, coefficient_budget=8192)
    ledger.max_nodes = ledger.nodes

    assert _lookup(memo, candidate) is None
    assert (
        ledger.counters.get(_collatz_keys.COLLATZ_CONDITIONAL_SCHEDULER_CACHE_BYPASSES)
        == 1
    )

    ledger.max_nodes = None
    assert _lookup(memo, candidate) is candidate
    memo.close()
    assert ledger.entries == ledger.nodes == 0


def test_lookup_exception_closes_reservation_before_propagating() -> None:
    candidate = _candidate()
    ledger = ResourceLedger()
    memo = ConditionalSchedulerMemo(ledger)
    memo.remember_port(candidate, demand=0, coefficient_budget=8192)
    original_admits = SourceClosedPortAction.admits

    def fail_during_reserved_lookup(port: SourceClosedPortAction, source: int) -> bool:
        if any(account.nodes > 0 for account in _lookup_accounts(ledger)):
            raise RuntimeError("injected lookup failure")
        return original_admits(port, source)

    with (
        patch.object(SourceClosedPortAction, "admits", fail_during_reserved_lookup),
        pytest.raises(RuntimeError, match="injected lookup failure"),
    ):
        _lookup(memo, candidate)

    memo.close()
    assert ledger.entries == ledger.nodes == 0


def test_close_retries_failed_memo_disposal_after_marking_scratch_owner() -> None:
    candidate = _candidate()
    ledger = ResourceLedger()
    memo = ConditionalSchedulerMemo(ledger)
    memo.remember_port(candidate, demand=0, coefficient_budget=8192)
    assert _lookup(memo, candidate) is candidate
    original_dispose = OwnedMemo[object, object].dispose
    should_fail = True

    def fail_once(owned: OwnedMemo[object, object]) -> None:
        nonlocal should_fail
        if should_fail:
            should_fail = False
            raise RuntimeError("injected memo disposal failure")
        original_dispose(owned)

    with patch.object(OwnedMemo, "dispose", fail_once):
        with pytest.raises(RuntimeError, match="injected memo disposal failure"):
            memo.close()
        assert all(row.disposed for row in _lookup_accounts(ledger))
        memo.close()

    assert ledger.entries == ledger.nodes == 0
    assert all(row.disposed for row in ledger.inventory())
