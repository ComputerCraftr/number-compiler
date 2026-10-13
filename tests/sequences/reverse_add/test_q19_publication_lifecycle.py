"""Adversarial publication and teardown checks for the Q19 output owner."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace

import pytest

from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditStoreBinding,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairOutputOccurrence,
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.source_images import (
    ReverseSourceImageWorkspace,
)


def _q19_workspace() -> tuple[ReverseSourceImageWorkspace, ReversePairQ19OutputOwner]:
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 3)
    tuple(workspace.iter_digits())
    owner = workspace.adapter._q19_owner
    assert owner is not None
    return workspace, owner


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


def test_q19_constructor_rolls_back_if_audit_publication_fails_after_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owners: list[ReversePairQ19OutputOwner] = []
    construction_error = RuntimeError("injected audit publication failure")
    original_register = ResourceLedger.register_payload_audit_contract

    def publish_then_fail(
        target_ledger: ResourceLedger,
        root: object,
        family: str,
        stores: tuple[PayloadAuditStoreBinding, ...],
        validator: Callable[[object, object], PayloadAuditContribution],
        *,
        dependencies: tuple[object, ...] = (),
    ) -> None:
        original_register(
            target_ledger,
            root,
            family,
            stores,
            validator,
            dependencies=dependencies,
        )
        assert isinstance(root, ReversePairQ19OutputOwner)
        owners.append(root)
        raise construction_error

    monkeypatch.setattr(
        ResourceLedger, "register_payload_audit_contract", publish_then_fail
    )
    with pytest.raises(RuntimeError, match="injected audit publication failure"):
        ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)

    assert len(owners) == 1
    owner = owners[0]
    assert owner._disposed and owner._cleanup_complete
    assert (id(owner), "reverse_add") not in ledger._payload_audit_contracts
    assert ledger.audit_payload_contracts().invalid == frozenset()
    assert ledger.entries == ledger.nodes == 0
