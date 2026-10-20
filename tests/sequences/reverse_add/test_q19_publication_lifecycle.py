"""Adversarial publication and teardown checks for the Q19 output owner."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.ledger import (
    ResourceLedger,
    ResourceScope,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairOutputOccurrence,
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.q19_output_contracts import (
    ReversePairQ19OutputAuditSnapshot,
)
from number_compiler.sequences.reverse_add.source_images import (
    ReverseSourceImageWorkspace,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from tests.support.owned_memo_failures import fail_owned_memo_dispose_once
from tests.support.payload_audit_failures import (
    assert_payload_publication_released,
    fail_after_payload_audit_publication,
)


def _assert_subordinate_cleanup(state: ReversePairQ19OutputAuditSnapshot) -> None:
    assert state.summaries.disposed
    assert all(
        memo.disposed
        for memo in (
            state.projector_forward,
            state.projector_reverse,
            state.projector_block,
            state.projector_forward_power,
            state.projector_reverse_power,
        )
    )
    assert state.arena.audit_snapshot().cleanup_complete is True


def _q19_workspace() -> tuple[ReverseSourceImageWorkspace, ReversePairQ19OutputOwner]:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
    tuple(workspace.iter_digits())
    owner = workspace.adapter.audit_snapshot().q19_owner
    assert owner is not None
    return workspace, owner


def _fail_port_disposal_once(
    monkeypatch: pytest.MonkeyPatch,
    ports: SourceCarryPorts,
    failure: OSError,
) -> None:
    original_dispose = SourceCarryPorts.dispose
    failed_once = False

    def fail_once(target: SourceCarryPorts) -> None:
        nonlocal failed_once
        if target is ports and not failed_once:
            failed_once = True
            raise failure
        original_dispose(target)

    monkeypatch.setattr(SourceCarryPorts, "dispose", fail_once)


def test_successful_q19_construction_keeps_its_owners_open() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)
    try:
        state = owner.audit_snapshot()
        assert not state.disposed
        assert not state.cleanup_complete
        assert not state.issued.disposed
        assert ledger.audit_payload_contracts().owns_root(
            "reverse_add", owner, ledger=ledger
        )
        assert ledger.entries > 0 and ledger.nodes > 0
    finally:
        owner.dispose()
    assert owner.audit_snapshot().cleanup_complete
    assert not ledger.audit_payload_contracts().owns_root(
        "reverse_add", owner, ledger=ledger
    )
    assert ledger.audit_payload_contracts().invalid == frozenset()
    assert ledger.entries == ledger.nodes == 0


def test_issued_occurrence_rejects_mutated_public_metadata_without_refolding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace, owner = _q19_workspace()
    occurrence = owner.initial

    def forbidden_refold(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("issued-handle validation refolded the Q19 grammar")

    monkeypatch.setattr(ReversePairQ19OutputOwner, "_full_summary", forbidden_refold)
    owner.validate_issued_occurrence(occurrence)
    object.__setattr__(occurrence, "pair_width", occurrence.pair_width - 1)
    with pytest.raises(ValueError, match="metadata was altered"):
        owner.validate_issued_occurrence(occurrence)
    with pytest.raises(ValueError, match="metadata was altered"):
        owner.validate(occurrence)
    workspace.dispose()
    assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_q19_walk_stack_obeys_tightened_node_budget_and_rolls_back() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)
    before_entries, before_nodes = ledger.entries, ledger.nodes
    assert owner.arena.nodes[owner.initial.root].kind == "CONCAT"
    ledger.max_nodes = before_nodes + 1
    stream = owner.iter_pair_values(owner.initial)

    with pytest.raises(BlockContextBudgetExceeded):
        next(stream)

    assert ledger.entries == before_entries
    assert ledger.nodes == before_nodes
    owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_deferred_q19_scratch_disposal_can_be_retried_after_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)
    stream = owner.iter_pair_values(owner.initial)
    next(stream)
    original_mark_disposed = ledger.mark_disposed
    failed_once = False

    def fail_scratch_once(resource_owner: int) -> None:
        nonlocal failed_once
        if resource_owner == owner.scratch_owner and not failed_once:
            failed_once = True
            raise RuntimeError("injected deferred scratch disposal failure")
        original_mark_disposed(resource_owner)

    monkeypatch.setattr(ledger, "mark_disposed", fail_scratch_once)
    owner.dispose()
    assert not owner.audit_snapshot().cleanup_complete
    with pytest.raises(RuntimeError, match="deferred scratch disposal"):
        next(stream)
    assert not owner.audit_snapshot().cleanup_complete

    monkeypatch.setattr(ledger, "mark_disposed", original_mark_disposed)
    owner.dispose()
    assert owner.audit_snapshot().cleanup_complete
    assert ledger.entries == ledger.nodes == 0


def test_failed_growth_admission_does_not_publish_candidate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace, owner = _q19_workspace()
    try:
        before = set(owner.audit_snapshot().issued.payload_view)
        exact_candidate = owner.candidate

        def overstate_growth(
            root: int, temporal_steps: int
        ) -> ReversePairOutputOccurrence:
            candidate = exact_candidate(root, temporal_steps)
            return replace(
                candidate,
                output_width=candidate.output_width + 2,
                growth=candidate.growth + 2,
            )

        monkeypatch.setattr(owner, "candidate", overstate_growth)
        with pytest.raises(AssertionError, match="one reverse/add step changed width"):
            owner.apply_pair_step(owner.initial)

        assert set(owner.audit_snapshot().issued.payload_view) == before
    finally:
        workspace.dispose()
        assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_q19_disposal_attempts_all_owners_and_retries_failed_release(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace, owner = _q19_workspace()
    try:
        before = owner.audit_snapshot()
        target_owner = before.issued_owner
        failure = OSError("injected occurrence-store disposal failure")
        injected = fail_owned_memo_dispose_once(
            monkeypatch, lambda memo: memo.owner == target_owner, failure
        )
        with pytest.raises(OSError) as caught:
            owner.dispose()
        assert caught.value is failure
        assert injected.triggered
        after_first_state = owner.audit_snapshot()
        assert after_first_state.disposed
        assert not after_first_state.cleanup_complete
        assert not after_first_state.issued.disposed
        _assert_subordinate_cleanup(after_first_state)

        owned_accounts = (
            {after_first_state.issued_owner, after_first_state.summary_owner}
            | set(after_first_state.projector_owners)
            | set(after_first_state.arena.owners)
            | {owner.scratch_owner}
        )
        after_first = {
            account.owner: account for account in workspace.ledger.inventory()
        }
        assert all(
            after_first[account].disposed
            and after_first[account].entries == 0
            and after_first[account].nodes == 0
            for account in owned_accounts - {target_owner}
        )

        owner.dispose()
        after_retry_state = owner.audit_snapshot()
        assert after_retry_state.cleanup_complete
        assert after_retry_state.issued.disposed
        after_retry = {
            account.owner: account for account in workspace.ledger.inventory()
        }
        assert all(
            after_retry[account].disposed
            and after_retry[account].entries == 0
            and after_retry[account].nodes == 0
            for account in owned_accounts
        )
    finally:
        workspace.dispose()
        assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_adapter_disposal_releases_q19_after_an_independent_port_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace, owner = _q19_workspace()
    adapter = workspace.adapter
    ports = adapter.ports(workspace.actions.source(workspace.source))
    failure = OSError("injected carry-port disposal failure")
    _fail_port_disposal_once(monkeypatch, ports, failure)
    try:
        with pytest.raises(OSError) as caught:
            adapter.dispose()
        assert caught.value is failure
        adapter_state = adapter.audit_snapshot()
        assert adapter_state.ports is ports
        assert adapter_state.q19_owner is None
        assert owner.audit_snapshot().cleanup_complete
        assert adapter_state.recursive_occurrences.disposed

        adapter.dispose()
        assert adapter.audit_snapshot().ports is None
    finally:
        workspace.dispose()
    assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_workspace_disposal_retries_failed_adapter_release(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace, owner = _q19_workspace()
    adapter = workspace.adapter
    ports = adapter.ports(workspace.actions.source(workspace.source))
    failure = OSError("injected workspace carry-port disposal failure")
    _fail_port_disposal_once(monkeypatch, ports, failure)
    try:
        with pytest.raises(OSError) as caught:
            workspace.dispose()
        assert caught.value is failure
        workspace_state = workspace.audit_snapshot()
        adapter_state = adapter.audit_snapshot()
        assert workspace_state.disposed and not workspace_state.cleanup_complete
        assert adapter_state.ports is ports
        assert adapter_state.q19_owner is None
        assert owner.audit_snapshot().cleanup_complete
        with pytest.raises(ValueError, match="disposed reverse source workspace"):
            workspace.width()

        workspace.dispose()
        assert workspace.audit_snapshot().cleanup_complete
        assert adapter.audit_snapshot().ports is None
    finally:
        if not workspace.audit_snapshot().cleanup_complete:
            workspace.dispose()
    assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_q19_constructor_keeps_construction_error_in_cleanup_chain(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owners: list[ReversePairQ19OutputOwner] = []
    construction_error = RuntimeError("injected initial construction failure")
    cleanup_error = OSError("injected rollback release failure")

    def fail_initial(owner: ReversePairQ19OutputOwner) -> ReversePairOutputOccurrence:
        owners.append(owner)
        raise construction_error

    injected = fail_owned_memo_dispose_once(
        monkeypatch,
        lambda memo: (
            bool(owners)
            and memo.ledger is ledger
            and ledger.account_status(memo.owner).role
            == "reverse_pair_output_occurrence"
        ),
        cleanup_error,
    )

    monkeypatch.setattr(ReversePairQ19OutputOwner, "_make_initial", fail_initial)
    with pytest.raises(OSError) as caught:
        ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)

    assert caught.value is cleanup_error
    assert injected.triggered
    assert caught.value.__cause__ is construction_error
    assert len(owners) == 1
    owner = owners[0]
    state = owner.audit_snapshot()
    assert state.initial is None
    assert state.disposed and not state.cleanup_complete
    _assert_subordinate_cleanup(state)

    owner.dispose()
    assert owner.audit_snapshot().cleanup_complete
    assert owner.audit_snapshot().issued.disposed
    assert ledger.entries == ledger.nodes == 0


def test_q19_partial_owner_setup_retires_registered_resources(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    construction_error = RuntimeError("injected projector owner registration failure")
    original_register = ResourceLedger.register

    def fail_projector_block(
        target_ledger: ResourceLedger,
        name: str,
        role: str,
        scope: ResourceScope = ResourceScope.ENGINE_OWNED,
    ) -> int:
        if name.endswith("-projector-block"):
            raise construction_error
        return original_register(target_ledger, name, role, scope)

    monkeypatch.setattr(ResourceLedger, "register", fail_projector_block)
    with pytest.raises(
        RuntimeError, match="injected projector owner registration"
    ) as caught:
        ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)

    assert caught.value is construction_error
    accounts = ledger.inventory()
    assert any(account.name.endswith("-projector-forward") for account in accounts)
    assert any(account.name.endswith("-projector-reverse") for account in accounts)
    assert not any(account.name.endswith("-projector-block") for account in accounts)
    assert all(
        account.disposed and account.entries == account.nodes == 0
        for account in accounts
    )
    assert ledger.entries == ledger.nodes == 0
    assert ledger.audit_payload_contracts().invalid == frozenset()


def test_q19_constructor_rolls_back_if_audit_publication_fails_after_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    construction_error = RuntimeError("injected audit publication failure")
    owners = fail_after_payload_audit_publication(monkeypatch, construction_error)
    with pytest.raises(RuntimeError, match="injected audit publication failure"):
        ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)

    assert len(owners) == 1
    owner = owners[0]
    assert isinstance(owner, ReversePairQ19OutputOwner)
    assert owner.audit_snapshot().disposed
    assert owner.audit_snapshot().cleanup_complete
    assert_payload_publication_released(ledger, owner, "reverse_add")
