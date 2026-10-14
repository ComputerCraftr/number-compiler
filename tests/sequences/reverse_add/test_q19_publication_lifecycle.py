"""Adversarial publication and teardown checks for the Q19 output owner."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.ledger import (
    OwnedMemo,
    ResourceLedger,
    ResourceScope,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairOutputOccurrence,
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.source_images import (
    ReverseSourceImageWorkspace,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from tests.support.payload_audit_failures import (
    assert_payload_publication_released,
    fail_after_payload_audit_publication,
)


def _q19_workspace() -> tuple[ReverseSourceImageWorkspace, ReversePairQ19OutputOwner]:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
    tuple(workspace.iter_digits())
    owner = workspace.adapter._q19_owner
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
    contract_key = (id(owner), "reverse_add")
    try:
        assert not owner._disposed
        assert not owner._cleanup_complete
        assert not owner._issued._disposed
        assert contract_key in ledger._payload_audit_contracts
        assert ledger.entries > 0 and ledger.nodes > 0
    finally:
        owner.dispose()
    assert owner._cleanup_complete
    assert contract_key not in ledger._payload_audit_contracts
    assert ledger.audit_payload_contracts().invalid == frozenset()
    assert ledger.entries == ledger.nodes == 0


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
        if resource_owner == owner._scratch_owner and not failed_once:
            failed_once = True
            raise RuntimeError("injected deferred scratch disposal failure")
        original_mark_disposed(resource_owner)

    monkeypatch.setattr(ledger, "mark_disposed", fail_scratch_once)
    owner.dispose()
    assert not owner._cleanup_complete
    with pytest.raises(RuntimeError, match="deferred scratch disposal"):
        next(stream)
    assert not owner._cleanup_complete

    monkeypatch.setattr(ledger, "mark_disposed", original_mark_disposed)
    owner.dispose()
    assert owner._cleanup_complete
    assert ledger.entries == ledger.nodes == 0


def test_failed_growth_admission_does_not_publish_candidate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace, owner = _q19_workspace()
    try:
        before = set(owner._issued)
        exact_candidate = owner._candidate

        def overstate_growth(
            root: int, temporal_steps: int
        ) -> ReversePairOutputOccurrence:
            candidate = exact_candidate(root, temporal_steps)
            return replace(
                candidate,
                output_width=candidate.output_width + 2,
                growth=candidate.growth + 2,
            )

        monkeypatch.setattr(owner, "_candidate", overstate_growth)
        with pytest.raises(AssertionError, match="one reverse/add step changed width"):
            owner.apply_pair_step(owner.initial)

        assert set(owner._issued) == before
    finally:
        workspace.dispose()
        assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_q19_disposal_attempts_all_owners_and_retries_failed_release(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace, owner = _q19_workspace()
    try:
        target = owner._issued
        original_dispose = OwnedMemo.dispose
        failure = OSError("injected occurrence-store disposal failure")
        failed_once = False

        def fail_once(memo: OwnedMemo[object, object]) -> None:
            nonlocal failed_once
            if memo is target and not failed_once:
                failed_once = True
                raise failure
            original_dispose(memo)

        monkeypatch.setattr(OwnedMemo, "dispose", fail_once)
        with pytest.raises(OSError) as caught:
            owner.dispose()
        assert caught.value is failure
        assert owner._disposed
        assert not owner._cleanup_complete
        assert not target._disposed
        assert owner._summaries._disposed
        assert all(memo._disposed for memo in owner._projector_memos)
        assert owner.arena._cleanup_complete

        owned_accounts = (
            {target.owner, owner._summaries.owner}
            | {memo.owner for memo in owner._projector_memos}
            | set(owner.arena.owners)
            | {owner._scratch_owner}
        )
        after_first = {
            account.owner: account for account in workspace.ledger.inventory()
        }
        assert all(
            after_first[account].disposed
            and after_first[account].entries == 0
            and after_first[account].nodes == 0
            for account in owned_accounts - {target.owner}
        )

        owner.dispose()
        assert owner._cleanup_complete
        assert target._disposed
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
        assert adapter._ports is ports
        assert adapter._q19_owner is None
        assert owner._cleanup_complete
        assert adapter._recursive_occurrences._disposed

        adapter.dispose()
        assert adapter._ports is None
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
        assert workspace._disposed and not workspace._cleanup_complete
        assert adapter._ports is ports
        assert adapter._q19_owner is None
        assert owner._cleanup_complete
        with pytest.raises(ValueError, match="disposed reverse source workspace"):
            workspace.width()

        workspace.dispose()
        assert workspace._cleanup_complete
        assert adapter._ports is None
    finally:
        if not workspace._cleanup_complete:
            workspace.dispose()
    assert workspace.ledger.entries == workspace.ledger.nodes == 0


def test_q19_constructor_keeps_construction_error_in_cleanup_chain(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owners: list[ReversePairQ19OutputOwner] = []
    construction_error = RuntimeError("injected initial construction failure")
    cleanup_error = OSError("injected rollback release failure")
    failed_once = False

    def fail_initial(owner: ReversePairQ19OutputOwner) -> ReversePairOutputOccurrence:
        owners.append(owner)
        raise construction_error

    original_dispose = OwnedMemo.dispose

    def fail_once(memo: OwnedMemo[object, object]) -> None:
        nonlocal failed_once
        if owners and memo is owners[0]._issued and not failed_once:
            failed_once = True
            raise cleanup_error
        original_dispose(memo)

    monkeypatch.setattr(ReversePairQ19OutputOwner, "_make_initial", fail_initial)
    monkeypatch.setattr(OwnedMemo, "dispose", fail_once)
    with pytest.raises(OSError) as caught:
        ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)

    assert caught.value is cleanup_error
    assert caught.value.__cause__ is construction_error
    assert len(owners) == 1
    owner = owners[0]
    assert owner._disposed and not owner._cleanup_complete
    assert owner._summaries._disposed
    assert all(memo._disposed for memo in owner._projector_memos)
    assert owner.arena._cleanup_complete

    owner.dispose()
    assert owner._cleanup_complete
    assert owner._issued._disposed
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
        scope: ResourceScope = "ENGINE_OWNED",
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
    assert owner._disposed and owner._cleanup_complete
    assert_payload_publication_released(ledger, owner, "reverse_add")
