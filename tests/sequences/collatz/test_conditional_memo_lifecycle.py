"""Temporary lookup workspaces belong to each conditional memo's lifecycle."""

from dataclasses import replace
from unittest.mock import patch

import pytest

from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import (
    LedgerReservation,
    OwnedMemo,
    ResourceLedger,
)
from number_compiler.resources.ledger_records import ResourceInventory
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_harmonic_ring import (
    ConstantTail6305Ring,
    PeriodicTail6305Ring,
)
from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
    CertifiedSchedulerCandidate,
    issue_conditional_scheduler_candidate,
)
from number_compiler.sequences.collatz.conditional_scheduler_memo import (
    ConditionalSchedulerMemo,
)
from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape
from number_compiler.sequences.collatz.source_closed_port_action import (
    SourceClosedPortAction,
)
from tests.support.reference_arithmetic import normalized_collatz_word


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


def _joint_candidate() -> tuple[
    CertifiedSchedulerCandidate, ResourceLedger, ParityCarryTape
]:
    residue, modulus = ConstantTail6305Ring.guard_residue(0, 64)
    source = residue + modulus * (5 * (1 << 172) + 1)
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "conditional-joint-memo-test")
    with scratch.scope():
        candidate = issue_conditional_scheduler_candidate(
            source,
            256,
            scratch=scratch,
            ledger=ledger,
            max_coefficient_bits=8192,
            include_f5=True,
            include_joint=True,
        )
    assert candidate is not None and candidate.joined_port is not None
    endpoint, bits = normalized_collatz_word(source, candidate.normalized_steps)
    assert endpoint == candidate.endpoint
    # This producer intentionally supplies no retained grammar. Construct an
    # independent literal test witness, then admit it through the actual
    # GuardedPortJoin constructor so the cold fold/action check issues its
    # binding. The fixture never supplies production authority directly.
    words = tuple(
        ParityCarryTape.letters(bits[offset : offset + 64])
        for offset in range(0, len(bits), 64)
    )
    tape = ParityCarryTape.sequence(words)
    joined = replace(candidate.joined_port, parity_tape=tape)
    candidate = replace(candidate, joined_port=joined)
    assert candidate.joined_port is not None
    assert tape.action().coefficient_snapshot() == (
        candidate.joined_port.port.action.coefficient_snapshot()
    )
    return candidate, ledger, tape


def _rebuilt_tape(tape: ParityCarryTape) -> ParityCarryTape:
    bits = tape.prefix_letters(tape.steps)
    words = tuple(
        ParityCarryTape.letters(bits[offset : offset + 64])
        for offset in range(0, len(bits), 64)
    )
    return ParityCarryTape.sequence(words)


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


def test_warm_joined_memo_hit_checks_pinned_tape_without_refolding_action() -> None:
    candidate, ledger, tape = _joint_candidate()
    assert candidate.joined_port is not None
    with_tape_bits = candidate.verification_operand_bits(0)
    object.__setattr__(candidate.joined_port, "parity_tape", None)
    without_tape_bits = candidate.verification_operand_bits(0)
    object.__setattr__(candidate.joined_port, "parity_tape", tape)
    assert with_tape_bits > without_tape_bits
    memo = ConditionalSchedulerMemo(ledger)
    memo.remember_port(candidate, demand=0, coefficient_budget=8192)

    with patch.object(
        ParityCarryTape,
        "action",
        side_effect=AssertionError("memo hit refolded the parity tape"),
    ):
        assert _lookup(memo, candidate) is candidate

    memo.close()
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize(
    "tamper",
    (
        "replace",
        "factor_grammar",
        "named_macro",
        "factor_repetitions",
        "source",
        "phase",
    ),
)
def test_joined_candidate_memo_rejects_tape_or_selector_mutation(tamper: str) -> None:
    candidate, ledger, tape = _joint_candidate()
    joined = candidate.joined_port
    assert joined is not None
    memo = ConditionalSchedulerMemo(ledger)
    memo.remember_port(candidate, demand=0, coefficient_budget=8192)

    if tamper == "replace":
        object.__setattr__(joined, "parity_tape", _rebuilt_tape(tape))
    elif tamper == "factor_grammar":
        object.__setattr__(joined, "factor_grammar", object())
    elif tamper == "named_macro":
        object.__setattr__(joined, "named_macro", object())
    elif tamper == "factor_repetitions":
        object.__setattr__(joined, "factor_repetitions", 2)
    elif tamper == "source":
        object.__setattr__(candidate, "source", candidate.source + 1)
    else:
        object.__setattr__(candidate, "numerator_phase", object())

    with pytest.raises((TypeError, ValueError)):
        _lookup(memo, candidate)
    memo.close()
    assert ledger.entries == ledger.nodes == 0


def test_parity_tape_nodes_reject_nested_runtime_mutation() -> None:
    tape = ParityCarryTape.sequence(
        (ParityCarryTape.letters((1, 0)), ParityCarryTape.letters((0, 1)))
    )
    leaf = tape.children[0]
    original_action = tape.action()

    with pytest.raises((AttributeError, TypeError)):
        object.__setattr__(leaf, "word", tuple(bool(bit) for bit in leaf.word))
    with pytest.raises((AttributeError, TypeError)):
        object.__setattr__(tape, "children", (tape,))

    assert tape.action() == original_action


def test_joined_candidate_memo_seal_checks_tape_action_before_publication() -> None:
    candidate, ledger, _tape = _joint_candidate()
    joined = candidate.joined_port
    assert joined is not None
    wrong = ParityCarryTape.repeated(
        ParityCarryTape.letters((0,)), candidate.normalized_steps
    )
    object.__setattr__(joined, "parity_tape", wrong)
    memo = ConditionalSchedulerMemo(ledger)

    with pytest.raises((ValueError, ArithmeticError)):
        memo.remember_port(candidate, demand=0, coefficient_budget=8192)

    memo.close()
    assert ledger.entries == ledger.nodes == 0


def test_refused_or_failed_publication_does_not_retain_unowned_tape_snapshot() -> None:
    candidate, ledger, _tape = _joint_candidate()
    memo = ConditionalSchedulerMemo(ledger)
    ledger.max_nodes = ledger.nodes

    memo.remember_port(candidate, demand=0, coefficient_budget=8192)
    with pytest.raises(ValueError, match="memo issuance seal is invalid"):
        candidate.verify_memo_issued()

    ledger.max_nodes = None

    def fail_adoption(
        _owned: OwnedMemo[tuple[int, ...], object],
        _key: tuple[int, ...],
        _value: object,
        _reservation: LedgerReservation,
    ) -> None:
        raise RuntimeError("injected conditional memo publication failure")

    with (
        patch.object(OwnedMemo, "adopt_reserved", fail_adoption),
        pytest.raises(
            RuntimeError, match="injected conditional memo publication failure"
        ),
    ):
        memo.remember_port(candidate, demand=0, coefficient_budget=8192)
    with pytest.raises(ValueError, match="memo issuance seal is invalid"):
        candidate.verify_memo_issued()

    memo.close()
    assert ledger.entries == ledger.nodes == 0
