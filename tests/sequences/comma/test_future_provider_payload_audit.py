"""Payload integrity and lifecycle regressions for the FutureCID provider."""

from __future__ import annotations

from dataclasses import replace
from threading import RLock
from typing import TypeGuard, cast

import pytest

from number_compiler.arithmetic.contracts.input_validation import object_mapping
from number_compiler.resources.immutable_signature import ScalarSignature
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.owned_memo import DynamicMemoValue
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.comma import future_authority, future_provider
from number_compiler.sequences.comma.boundary_quotient import BoundaryState
from number_compiler.sequences.comma.future_authority import class_row_signature
from number_compiler.sequences.comma.future_provider_memory import (
    RetainedSemanticFutureProvider,
)
from tests.support.comma_future_provider_fixture import (
    candidate_record,
    install_synthetic_registry,
    provider_classes,
    provider_source_classes,
    work_log,
    workspace_owner,
)


def _is_retained_provider_memo_container(
    value: object,
) -> TypeGuard[
    LedgerDict[
        str,
        RetainedSemanticFutureProvider
        | DynamicMemoValue[RetainedSemanticFutureProvider],
    ]
]:
    mapping = object_mapping(value)
    if type(value) is not LedgerDict or mapping is None:
        return False
    return all(
        type(key) is str
        and (
            type(item) is RetainedSemanticFutureProvider
            or (
                type(item) is DynamicMemoValue
                and type(item.value) is RetainedSemanticFutureProvider
                and type(item.nodes) is int
            )
        )
        for key, item in mapping.items()
    )


def _assert_family_payload_invalid(ledger: ResourceLedger) -> None:
    invalid = ledger.audit_payload_contracts().family("comma", ledger=ledger)[1]
    assert invalid


def _assert_fresh_payload_audit_clean(ledger: ResourceLedger) -> None:
    restored = audit_registered_payloads(ledger, fresh=True)
    assert restored.unknown_payloads == 0
    assert restored.forbidden_future_payloads == 0


def _swap_provider_source_classes(
    provider: future_provider.SemanticFutureProvider,
    first_index: int,
    second_index: int,
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    original = provider_source_classes(provider)
    changed_values = list(original)
    changed_values[first_index], changed_values[second_index] = (
        changed_values[second_index],
        changed_values[first_index],
    )
    changed = tuple(changed_values)
    object.__setattr__(provider, "_source_classes", changed)
    object.__setattr__(provider, "_source_classes_binding", changed)
    return original, changed


def _restore_provider_source_classes(
    provider: future_provider.SemanticFutureProvider,
    sources: tuple[int, ...],
) -> None:
    object.__setattr__(provider, "_source_classes", sources)
    object.__setattr__(provider, "_source_classes_binding", sources)


def _assert_workspace_binding_rejected(
    store: future_provider.SemanticFutureProviderStore,
    digest: str,
    original_owner: int,
    attempted_owner: object,
) -> None:
    object.__setattr__(store, "_workspace_owner", attempted_owner)
    try:
        with pytest.raises(RuntimeError, match="workspace owner binding changed"):
            store.get(digest)
        _assert_family_payload_invalid(store.ledger)
    finally:
        object.__setattr__(store, "_workspace_owner", original_owner)
    _assert_fresh_payload_audit_clean(store.ledger)


def _retained_provider_entry(
    store: future_provider.SemanticFutureProviderStore,
) -> tuple[str, DynamicMemoValue[RetainedSemanticFutureProvider]]:
    entry_digest, stored = next(iter(store.audit_snapshot().memo.container.items()))
    if type(stored) is not DynamicMemoValue:
        raise AssertionError("provider store omitted its retained cost wrapper")
    return entry_digest, stored


def test_from_record_candidate_data_does_not_issue_execution_authority(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()
    _charges, charge_work = work_log()
    install_synthetic_registry(monkeypatch, record, charge_work)
    provider = future_provider.SemanticFutureProvider.from_record(
        record, charge_work=charge_work
    )

    source = BoundaryState("N", 2, 3)
    assert provider.source_class(source, charge_work=charge_work) == 2
    assert (
        provider.class_row(2, charge_work=charge_work) == provider_classes(provider)[2]
    )
    assert not provider.runtime_admitted
    with pytest.raises(PermissionError, match="kernel admission"):
        provider.select_unique_unranked_child(source, charge_work=charge_work)


def test_payload_admission_copy_cannot_mutate_registry_or_promote_fixture(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()
    _charges, charge_work = work_log()
    digest = install_synthetic_registry(monkeypatch, record, charge_work)
    store = future_provider.SemanticFutureProviderStore(ResourceLedger())
    lease = store.load_record(record, charge_work=charge_work)
    provider = lease.resolve_provider()
    copied = provider.audit_snapshot().admission
    assert future_provider.registered_admission_metadata_matches(copied, digest)
    original_copy_fields = (
        copied.artifact_sha256,
        copied.instance_id,
        copied.theorem_id,
        copied.contract_id,
        copied.claims,
        copied.scope,
    )

    object.__setattr__(
        copied, "instance_id", future_authority.GLOBAL_RELEASE_SESSION_ID
    )
    object.__setattr__(copied, "theorem_id", future_authority.GLOBAL_RELEASE_THEOREM_ID)
    object.__setattr__(
        copied, "contract_id", future_authority.GLOBAL_RELEASE_CONTRACT_ID
    )
    object.__setattr__(copied, "claims", future_authority.GLOBAL_RELEASE_CLAIMS)
    object.__setattr__(copied, "scope", future_authority.KERNEL_RELEASE_SCOPE)

    assert future_authority.global_release_admission_matches(copied, digest)
    assert not future_provider.registered_admission_metadata_matches(copied, digest)
    assert not provider.runtime_admitted
    assert not provider.global_release_admitted
    with pytest.raises(PermissionError, match="kernel admission"):
        store.get(digest)
    tampered_audit = audit_registered_payloads(store.ledger, fresh=True)
    assert tampered_audit.forbidden_future_payloads > 0

    object.__setattr__(copied, "instance_id", original_copy_fields[1])
    object.__setattr__(copied, "theorem_id", original_copy_fields[2])
    object.__setattr__(copied, "contract_id", original_copy_fields[3])
    object.__setattr__(copied, "claims", original_copy_fields[4])
    object.__setattr__(copied, "scope", original_copy_fields[5])
    assert future_provider.registered_admission_metadata_matches(copied, digest)
    assert provider.runtime_admitted
    assert not provider.global_release_admitted
    assert (
        audit_registered_payloads(store.ledger, fresh=True).forbidden_future_payloads
        == 0
    )
    store.close()


def test_retained_source_anchor_and_cost_wrapper_are_immutable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()
    _charges, charge_work = work_log()
    digest = install_synthetic_registry(monkeypatch, record, charge_work)
    store = future_provider.SemanticFutureProviderStore(ResourceLedger())
    store.load_record(record, charge_work=charge_work)

    entry_digest, stored = _retained_provider_entry(store)
    assert entry_digest == digest
    retained = stored.value
    provider = retained.provider
    original_sources, changed_sources = _swap_provider_source_classes(provider, 0, 1)
    assert original_sources[0] != original_sources[1]
    assert set(changed_sources) == set(original_sources)

    try:
        forged_retained = retained._replace(source_classes=changed_sources)
        with pytest.raises(AttributeError):
            object.__setattr__(retained, "source_classes", changed_sources)
        with pytest.raises(AttributeError):
            object.__setattr__(stored, "value", forged_retained)
        with pytest.raises(PermissionError, match="kernel admission"):
            store.get(digest)
    finally:
        _restore_provider_source_classes(provider, original_sources)

    assert store.get(digest).resolve_provider() is provider
    restored = audit_registered_payloads(store.ledger, fresh=True)
    assert restored.unknown_payloads == 0
    assert restored.forbidden_future_payloads == 0
    store.close()


def test_retained_store_rejects_source_map_and_matching_self_binding_tamper(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()
    _charges, charge_work = work_log()
    digest = install_synthetic_registry(monkeypatch, record, charge_work)
    store = future_provider.SemanticFutureProviderStore(ResourceLedger())
    lease = store.load_record(record, charge_work=charge_work)
    provider = lease.resolve_provider()
    source = BoundaryState("N", 2, 3)
    original_sources, _forged_sources = _swap_provider_source_classes(provider, 0, 3)
    assert not provider.runtime_admitted
    assert not lease.runtime_admitted
    with pytest.raises(PermissionError, match="table binding changed"):
        provider.source_class(source, charge_work=charge_work)
    with pytest.raises(PermissionError, match="kernel admission"):
        store.get(digest)
    _assert_family_payload_invalid(store.ledger)

    _restore_provider_source_classes(provider, original_sources)
    assert provider.runtime_admitted
    assert lease.source_class(source, charge_work=charge_work) == original_sources[3]
    _assert_fresh_payload_audit_clean(store.ledger)
    store.close()


def test_retained_store_rejects_coherent_class_and_signature_replacement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()
    _charges, charge_work = work_log()
    digest = install_synthetic_registry(monkeypatch, record, charge_work)
    store = future_provider.SemanticFutureProviderStore(ResourceLedger())
    lease = store.load_record(record, charge_work=charge_work)
    provider = lease.resolve_provider()
    original_classes = provider_classes(provider)
    original_signatures = cast(
        tuple[ScalarSignature, ...],
        object.__getattribute__(provider, "_class_signatures"),
    )
    changed_row = replace(original_classes[2], rank=17)
    forged_classes = (*original_classes[:2], changed_row, *original_classes[3:])
    forged_signatures = tuple(class_row_signature(row) for row in forged_classes)

    object.__setattr__(provider, "_classes", forged_classes)
    object.__setattr__(provider, "_classes_binding", forged_classes)
    object.__setattr__(provider, "_class_signatures", forged_signatures)
    object.__setattr__(provider, "_class_signatures_binding", forged_signatures)
    assert not provider.runtime_admitted
    assert not lease.runtime_admitted
    with pytest.raises(PermissionError, match="kernel admission"):
        lease.class_row(2, charge_work=charge_work)
    with pytest.raises(PermissionError, match="kernel admission"):
        store.get(digest)
    invalid = store.ledger.audit_payload_contracts().family(
        "comma", ledger=store.ledger
    )[1]
    assert invalid

    object.__setattr__(provider, "_classes", original_classes)
    object.__setattr__(provider, "_classes_binding", original_classes)
    object.__setattr__(provider, "_class_signatures", original_signatures)
    object.__setattr__(provider, "_class_signatures_binding", original_signatures)
    assert provider.runtime_admitted
    assert lease.class_row(2, charge_work=charge_work) == original_classes[2]
    assert (
        audit_registered_payloads(store.ledger, fresh=True).forbidden_future_payloads
        == 0
    )
    store.close()


def test_provider_store_payload_contract_checks_rows_charges_and_lifecycle(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()
    _charges, charge_work = work_log()
    digest = install_synthetic_registry(monkeypatch, record, charge_work)
    ledger = ResourceLedger(max_nodes=65_536, max_cache_entries=2)
    store = future_provider.SemanticFutureProviderStore(ledger)
    lease = store.load_record(record, charge_work=charge_work)
    provider = lease.resolve_provider()

    audit = audit_registered_payloads(ledger, fresh=True)
    assert audit.forbidden_future_payloads == 0

    control = provider_classes(provider)[2].control
    original_kind = control.kind
    object.__setattr__(control, "kind", "landmine")
    try:
        _assert_family_payload_invalid(ledger)
    finally:
        object.__setattr__(control, "kind", original_kind)
    _assert_fresh_payload_audit_clean(ledger)

    original_sources = provider_source_classes(provider)
    changed_head = 0 if original_sources[0] != 0 else 1
    changed_sources = (changed_head, *original_sources[1:])
    object.__setattr__(provider, "_source_classes", changed_sources)
    try:
        _assert_family_payload_invalid(ledger)
    finally:
        object.__setattr__(provider, "_source_classes", original_sources)
    _assert_fresh_payload_audit_clean(ledger)

    row = provider_classes(provider)[2]
    original_children = row.ordered_children
    object.__setattr__(row, "ordered_children", tuple(reversed(original_children)))
    try:
        _assert_family_payload_invalid(ledger)
    finally:
        object.__setattr__(row, "ordered_children", original_children)
    _assert_fresh_payload_audit_clean(ledger)

    original_classes = provider_classes(provider)
    object.__setattr__(provider, "_classes", tuple(reversed(original_classes)))
    try:
        _assert_family_payload_invalid(ledger)
    finally:
        object.__setattr__(provider, "_classes", original_classes)
    _assert_fresh_payload_audit_clean(ledger)

    entry_digest, stored = _retained_provider_entry(store)
    assert entry_digest == digest
    original_nodes = stored.nodes
    with pytest.raises(AttributeError):
        object.__setattr__(stored, "nodes", original_nodes + 1)

    # Inject a malformed wrapper through the exact ledger snapshot map to
    # retain an independent regression for accounting drift at that boundary.
    malformed = DynamicMemoValue(stored.value, original_nodes + 1)
    memo_container: object = store.audit_snapshot().memo.container
    assert _is_retained_provider_memo_container(memo_container)
    memo_container[digest] = malformed
    try:
        _assert_family_payload_invalid(ledger)
    finally:
        memo_container[digest] = stored
    _assert_fresh_payload_audit_clean(ledger)

    object.__setattr__(store, "_untracked_provider_cache", {})
    try:
        _assert_family_payload_invalid(ledger)
    finally:
        object.__delattr__(store, "_untracked_provider_cache")
    _assert_fresh_payload_audit_clean(ledger)

    foreign_workspace = ledger.register(
        "test-foreign-future-provider-workspace",
        future_provider.FUTURE_PROVIDER_WORKSPACE_ROLE,
    )
    original_workspace_owner = store.audit_snapshot().workspace_owner
    _assert_workspace_binding_rejected(
        store, digest, original_workspace_owner, foreign_workspace
    )
    _assert_workspace_binding_rejected(
        store, digest, original_workspace_owner, bool(original_workspace_owner)
    )

    with monkeypatch.context() as patcher:
        patcher.setattr(store, "_lock", RLock())
        with pytest.raises(RuntimeError, match="lock binding changed"):
            store.get(digest)
        _assert_family_payload_invalid(ledger)
    _assert_fresh_payload_audit_clean(ledger)

    original_memo = object.__getattribute__(store, "_providers")
    object.__setattr__(store, "_providers", object())
    try:
        with pytest.raises(RuntimeError, match="authority binding changed"):
            store.get(digest)
        _assert_family_payload_invalid(ledger)
    finally:
        object.__setattr__(store, "_providers", original_memo)
    _assert_fresh_payload_audit_clean(ledger)

    assert provider.artifact_sha256 == digest
    store.reset()
    assert not lease.runtime_admitted
    restored = audit_registered_payloads(ledger, fresh=True)
    assert restored.unknown_payloads == 0
    assert restored.forbidden_future_payloads == 0
    store.close()
    restored = audit_registered_payloads(ledger, fresh=True)
    assert restored.unknown_payloads == 0
    assert restored.forbidden_future_payloads == 0


def test_provider_store_close_failure_restores_contract_and_retries(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()
    _charges, charge_work = work_log()
    digest = install_synthetic_registry(monkeypatch, record, charge_work)
    ledger = ResourceLedger(max_nodes=65_536, max_cache_entries=2)
    store = future_provider.SemanticFutureProviderStore(ledger)
    lease = store.load_record(record, charge_work=charge_work)
    provider = lease.resolve_provider()
    original_dispose = OwnedMemo[object, object].dispose
    failed = False
    retained_usage = ledger.account_usage(store.owner)

    def fail_once(memo: OwnedMemo[object, object]) -> None:
        nonlocal failed
        if memo.owner == store.owner and not failed:
            failed = True
            raise RuntimeError("injected provider memo disposal failure")
        original_dispose(memo)

    with monkeypatch.context() as patcher:
        patcher.setattr(OwnedMemo, "dispose", fail_once)
        with pytest.raises(
            RuntimeError, match="injected provider memo disposal failure"
        ):
            store.close()

    assert failed
    with pytest.raises(RuntimeError, match="closing or closed"):
        store.get(digest)
    with pytest.raises(RuntimeError, match="closing or closed"):
        store.load_record(record, charge_work=charge_work)
    with pytest.raises(RuntimeError, match="closing or closed"):
        store.reset()
    with pytest.raises(RuntimeError, match="stale"):
        lease.class_row(2, charge_work=charge_work)
    assert not lease.runtime_admitted
    assert ledger.account_usage(store.owner) == retained_usage
    audit = audit_registered_payloads(ledger, fresh=True)
    assert audit.unknown_payloads == 0
    assert audit.forbidden_future_payloads == 0

    original_sources, _forged_sources = _swap_provider_source_classes(provider, 0, 3)
    tampered_audit = audit_registered_payloads(ledger, fresh=True)
    assert tampered_audit.forbidden_future_payloads > 0
    _restore_provider_source_classes(provider, original_sources)
    restored_audit = audit_registered_payloads(ledger, fresh=True)
    assert restored_audit.unknown_payloads == 0
    assert restored_audit.forbidden_future_payloads == 0

    store.close()
    assert audit_registered_payloads(ledger, fresh=True).unknown_payloads == 0
    assert ledger.counters["comma_future_provider_closes"] == 1


def test_store_cancellation_releases_workspace_without_validation_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()

    def no_work(_amount: int) -> None:
        return None

    install_synthetic_registry(monkeypatch, record, no_work)
    ledger = ResourceLedger(max_nodes=65_536, max_cache_entries=2)
    store = future_provider.SemanticFutureProviderStore(ledger)

    class LoadCancelled(BaseException):
        pass

    def cancel_load(_amount: int) -> None:
        raise LoadCancelled

    with pytest.raises(LoadCancelled):
        store.load_record(record, charge_work=cancel_load)

    assert ledger.entries == ledger.nodes == 0
    workspace = ledger.inventory_owner(workspace_owner(ledger))
    assert workspace.nodes == 0
    assert ledger.counters["comma_future_provider_load_cancellations"] == 1
    assert ledger.counters.get("comma_future_provider_load_failures", 0) == 0
    store.close()
