from __future__ import annotations

import gc
from typing import cast
from weakref import ReferenceType

import pytest

from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContractAudit,
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
)
from number_compiler.resources.stores import LedgerList

_FAMILY_MODULE = "number_compiler.sequences.antihydra.contract_fixture"


class _FamilyRoot:
    __module__ = _FAMILY_MODULE

    def __init__(self, ledger: ResourceLedger, owner: int) -> None:
        self.ledger = ledger
        self.records: LedgerList[object] = ledger.make_list(owner)
        self.proposal = PayloadAuditContribution()


class _MemoFamilyRoot:
    __module__ = _FAMILY_MODULE

    def __init__(self, ledger: ResourceLedger, owner: int) -> None:
        self.ledger = ledger
        self.memo: OwnedMemo[str, object] = OwnedMemo(
            ledger, owner, node_cost=lambda _key, _value: 2
        )
        self.records = self.memo.audit_snapshot().container
        self.proposal = PayloadAuditContribution()


class _PinnedFamilyRoot(_FamilyRoot):
    __module__ = _FAMILY_MODULE

    def __init__(self, ledger: ResourceLedger, owner: int) -> None:
        super().__init__(ledger, owner)
        self.lock = object()
        self.workspace_owner = owner


def _fixture_validator(ledger: object, root: object) -> PayloadAuditContribution:
    del ledger
    return cast(_FamilyRoot, root).proposal


_fixture_validator.__module__ = _FAMILY_MODULE


def _bound_root() -> tuple[ResourceLedger, _FamilyRoot, int]:
    ledger = ResourceLedger()
    owner = ledger.register("family-records", "family_payload")
    root = _FamilyRoot(ledger, owner)
    ledger.register_execution_root(root)
    return ledger, root, owner


def _register(
    ledger: ResourceLedger, root: _FamilyRoot | _MemoFamilyRoot, owner: int
) -> None:
    ledger.register_payload_audit_contract(
        root,
        "antihydra",
        (PayloadAuditStoreBinding(owner, "records", "family_payload"),),
        _fixture_validator,
    )


@pytest.mark.parametrize("nested", (False, True))
def test_dynamic_memo_contract_only_unwraps_accounting_envelope(nested: bool) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("dynamic-family-records", "family_payload")
    root = _MemoFamilyRoot(ledger, owner)
    ledger.register_execution_root(root)
    value = object()
    root.memo["payload"] = (value,) if nested else value
    root.proposal = PayloadAuditContribution(
        approved=(PayloadAuditEntry(owner, value),)
    )
    _register(ledger, root, owner)

    result = ledger.audit_payload_contracts()

    assert ((owner, id(value)) in result.approved) is not nested
    assert bool(result.invalid) is nested
    assert ledger.account_status(owner).nodes == 3
    root.memo.clear()
    assert not result.approved


def test_contract_approves_only_concrete_members_of_its_bound_store() -> None:
    ledger, root, owner = _bound_root()
    value = object()
    ledger.reserve(owner, entries=1, nodes=1)
    root.records.append(value)
    root.proposal = PayloadAuditContribution(
        approved=(PayloadAuditEntry(owner, value),)
    )
    _register(ledger, root, owner)
    before_counters = dict(ledger.counters)

    result = ledger.audit_payload_contracts()

    assert result.approved == frozenset(((owner, id(value)),))
    assert result.invalid == frozenset()
    after_counters = dict(ledger.counters)
    assert after_counters.get("payload_audit_contract_member_visits", 0) == (
        before_counters.get("payload_audit_contract_member_visits", 0) + 1
    )
    assert {
        key: count
        for key, count in after_counters.items()
        if key != "payload_audit_contract_member_visits"
    } == {
        key: count
        for key, count in before_counters.items()
        if key != "payload_audit_contract_member_visits"
    }


def test_contract_pins_identity_and_typed_scalar_root_authority() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("pinned-family-records", "family_payload")
    root = _PinnedFamilyRoot(ledger, owner)
    ledger.register_execution_root(root)
    value = object()
    ledger.reserve(owner, entries=1, nodes=1)
    root.records.append(value)
    root.proposal = PayloadAuditContribution(
        approved=(PayloadAuditEntry(owner, value),)
    )
    ledger.register_payload_audit_contract(
        root,
        "antihydra",
        (
            PayloadAuditStoreBinding(
                owner,
                "records",
                "family_payload",
                identity_attributes=("lock",),
                scalar_attributes=("workspace_owner",),
            ),
        ),
        _fixture_validator,
    )

    assert ledger.payload_audit_contract_matches_root(root, "antihydra")
    assert ledger.audit_payload_contracts().approved == frozenset(((owner, id(value)),))

    original_lock = root.lock
    object.__setattr__(root, "lock", object())
    assert not ledger.payload_audit_contract_matches_root(root, "antihydra")
    assert not ledger.payload_audit_contract_matches_attribute(
        root, "antihydra", "lock"
    )
    assert (owner, id(root)) in ledger.audit_payload_contracts().invalid
    object.__setattr__(root, "lock", original_lock)

    object.__setattr__(root, "workspace_owner", bool(owner))
    assert not ledger.payload_audit_contract_matches_root(root, "antihydra")
    assert not ledger.payload_audit_contract_matches_attribute(
        root, "antihydra", "workspace_owner"
    )
    assert (owner, id(root)) in ledger.audit_payload_contracts().invalid
    object.__setattr__(root, "workspace_owner", owner)
    assert ledger.payload_audit_contract_matches_root(root, "antihydra")


def test_payload_audit_consumes_owner_qualified_contract_results() -> None:
    from number_compiler.resources.payload_audit import audit_registered_payloads

    ledger, root, owner = _bound_root()
    value = object()
    ledger.reserve(owner, entries=1, nodes=1)
    root.records.append(value)
    root.proposal = PayloadAuditContribution(
        approved=(PayloadAuditEntry(owner, value),)
    )
    _register(ledger, root, owner)

    audit = audit_registered_payloads(ledger)

    assert audit.unknown_payloads == 0
    assert audit.forbidden_future_payloads == 0


def test_contract_approval_does_not_escape_through_a_foreign_owner_alias() -> None:
    from number_compiler.resources.payload_audit import audit_registered_payloads

    ledger, root, owner = _bound_root()
    value = object()
    ledger.reserve(owner, entries=1, nodes=1)
    root.records.append(value)
    alias_owner = ledger.register("foreign-alias", "family_payload")
    alias: LedgerList[object] = ledger.make_list(alias_owner)
    ledger.reserve(alias_owner, entries=1, nodes=1)
    alias.append(value)
    root.proposal = PayloadAuditContribution(
        approved=(PayloadAuditEntry(owner, value),)
    )
    _register(ledger, root, owner)

    audit = audit_registered_payloads(ledger)

    assert audit.unknown_payloads > 0


@pytest.mark.parametrize(
    "forged",
    [
        "identity",
        "foreign_value",
        "foreign_none",
        "foreign_owner",
        "bound_root",
        "bound_store",
        "direct_bound_root",
        "direct_bound_store",
    ],
)
def test_contract_rejects_forged_or_foreign_approvals(forged: str) -> None:
    ledger, root, owner = _bound_root()
    value = object()
    ledger.reserve(owner, entries=1, nodes=1)
    target = (
        root
        if forged == "direct_bound_root"
        else root.records
        if forged == "direct_bound_store"
        else value
    )
    root.records.append(target)
    if forged == "identity":
        entry: object = id(value)
    elif forged == "foreign_value":
        entry = PayloadAuditEntry(owner, object())
    elif forged == "foreign_none":
        entry = PayloadAuditEntry(owner, None)
    elif forged == "foreign_owner":
        other_owner = ledger.register("foreign-records", "family_payload")
        entry = PayloadAuditEntry(other_owner, value)
    elif forged == "bound_root" or forged == "direct_bound_root":
        entry = PayloadAuditEntry(owner, root)
    elif forged == "direct_bound_store":
        entry = PayloadAuditEntry(owner, root.records)
    else:
        entry = PayloadAuditEntry(owner, root.records)
    proposal = PayloadAuditContribution()
    # Simulate a forged runtime result beyond the statically typed API.
    object.__setattr__(proposal, "approved", (entry,))
    root.proposal = proposal
    _register(ledger, root, owner)

    result = ledger.audit_payload_contracts()

    assert result.approved == frozenset()
    assert (owner, id(root)) in result.invalid


@pytest.mark.parametrize("snapshot_kind", ("stale", "foreign"))
def test_higher_audit_reacquires_an_invalid_contract_snapshot(
    snapshot_kind: str,
) -> None:
    from number_compiler.resources.higher_payload_audit import audit_higher_payloads

    ledger, root, owner = _bound_root()
    ledger.reserve(owner, entries=1, nodes=1)
    value = object()
    root.records.append(value)
    root.proposal = PayloadAuditContribution(
        approved=(PayloadAuditEntry(owner, object()),)
    )
    _register(ledger, root, owner)
    previous = ledger.audit_payload_contracts()
    assert previous.invalid
    if snapshot_kind == "stale":
        ledger.note_store_mutation()
    else:
        previous = ResourceLedger().audit_payload_contracts()

    result = audit_higher_payloads(ledger, previous)

    assert (owner, id(root)) in result.invalid


def _register_dependent_parent(
    ledger: ResourceLedger, child: _FamilyRoot
) -> tuple[_FamilyRoot, int]:
    parent_owner = ledger.register("parent-records", "family_payload")
    parent = _FamilyRoot(ledger, parent_owner)
    ledger.register_execution_root(parent)
    ledger.register_payload_audit_contract(
        parent,
        "antihydra",
        (PayloadAuditStoreBinding(parent_owner, "records", "family_payload"),),
        _fixture_validator,
        dependencies=(child,),
    )
    return parent, parent_owner


def test_payload_contract_dependency_accepts_a_clean_child_root() -> None:
    ledger, child, child_owner = _bound_root()
    _register(ledger, child, child_owner)
    parent, _parent_owner = _register_dependent_parent(ledger, child)

    result = ledger.audit_payload_contracts()

    assert result.owns_root("antihydra", child, ledger=ledger)
    assert result.owns_root("antihydra", parent, ledger=ledger)


def test_payload_contract_dependencies_propagate_invalid_child_authority() -> None:
    ledger, child, child_owner = _bound_root()
    _register(ledger, child, child_owner)
    parent, parent_owner = _register_dependent_parent(ledger, child)

    child.proposal = PayloadAuditContribution(
        approved=(PayloadAuditEntry(child_owner, object()),)
    )
    result = ledger.audit_payload_contracts()

    assert (parent_owner, id(parent)) in result.invalid
    assert not result.owns_root("antihydra", parent, ledger=ledger)


def test_payload_contract_dependency_becomes_invalid_when_child_registration_is_removed() -> (
    None
):
    ledger, child, child_owner = _bound_root()
    _register(ledger, child, child_owner)
    parent, parent_owner = _register_dependent_parent(ledger, child)
    ledger.remove_payload_audit_contract(child, "antihydra")

    result = ledger.audit_payload_contracts()

    assert (parent_owner, id(parent)) in result.invalid
    assert not result.owns_root("antihydra", parent, ledger=ledger)


def test_payload_contract_dependencies_reject_dangling_and_cyclic_roots() -> None:
    ledger, child, child_owner = _bound_root()
    parent_owner = ledger.register("parent-records", "family_payload")
    parent = _FamilyRoot(ledger, parent_owner)
    ledger.register_execution_root(parent)
    with pytest.raises(ValueError, match="exact live contracted root"):
        ledger.register_payload_audit_contract(
            parent,
            "antihydra",
            (PayloadAuditStoreBinding(parent_owner, "records", "family_payload"),),
            _fixture_validator,
            dependencies=(child,),
        )

    _register(ledger, child, child_owner)
    ledger.register_payload_audit_contract(
        parent,
        "antihydra",
        (PayloadAuditStoreBinding(parent_owner, "records", "family_payload"),),
        _fixture_validator,
        dependencies=(child,),
    )
    ledger.remove_payload_audit_contract(child, "antihydra")
    with pytest.raises(ValueError, match="dependency cycle"):
        ledger.register_payload_audit_contract(
            child,
            "antihydra",
            (PayloadAuditStoreBinding(child_owner, "records", "family_payload"),),
            _fixture_validator,
            dependencies=(parent,),
        )


def test_contract_invalid_entry_overrides_approval_for_same_object() -> None:
    ledger, root, owner = _bound_root()
    value = object()
    ledger.reserve(owner, entries=1, nodes=1)
    root.records.append(value)
    entry = PayloadAuditEntry(owner, value)
    root.proposal = PayloadAuditContribution(approved=(entry,), invalid=(entry,))
    _register(ledger, root, owner)

    result = ledger.audit_payload_contracts()

    assert (owner, id(value)) not in result.approved
    assert (owner, id(value)) in result.invalid
    assert not result.owns_root("antihydra", root, ledger=ledger)


def test_contract_rejects_stale_root_store_binding_and_wrong_role() -> None:
    ledger, root, owner = _bound_root()
    with pytest.raises(ValueError, match="exact live owner"):
        ledger.register_payload_audit_contract(
            root,
            "antihydra",
            (PayloadAuditStoreBinding(owner, "records", "wrong_role"),),
            _fixture_validator,
        )
    _register(ledger, root, owner)
    object.__setattr__(root, "records", [])

    result = ledger.audit_payload_contracts()

    assert result.approved == frozenset()
    assert (owner, id(root)) in result.invalid


def test_contract_requires_matching_family_function_and_live_exact_root() -> None:
    ledger, root, owner = _bound_root()

    def local_validator(ledger: object, root: object) -> PayloadAuditContribution:
        del ledger, root
        return PayloadAuditContribution()

    with pytest.raises(ValueError, match="module functions"):
        ledger.register_payload_audit_contract(
            root,
            "antihydra",
            (PayloadAuditStoreBinding(owner, "records", "family_payload"),),
            local_validator,
        )

    unrelated = ResourceLedger()
    with pytest.raises(ValueError, match="already be registered"):
        unrelated.register_payload_audit_contract(
            root,
            "antihydra",
            (PayloadAuditStoreBinding(owner, "records", "family_payload"),),
            _fixture_validator,
        )

    retained_source = object()

    def capturing_validator(ledger: object, root: object) -> PayloadAuditContribution:
        del ledger, root
        return PayloadAuditContribution(
            invalid=(PayloadAuditEntry(owner, retained_source),)
        )

    capturing_validator.__module__ = _FAMILY_MODULE
    with pytest.raises(ValueError, match="module functions"):
        ledger.register_payload_audit_contract(
            root,
            "antihydra",
            (PayloadAuditStoreBinding(owner, "records", "family_payload"),),
            capturing_validator,
        )


def test_contract_removal_and_owner_disposal_invalidate_registration() -> None:
    ledger, root, owner = _bound_root()
    _register(ledger, root, owner)
    registered_version = ledger.mutation_version

    ledger.remove_payload_audit_contract(root, "antihydra")

    assert ledger.mutation_version > registered_version
    assert ledger.audit_payload_contracts().approved == frozenset()
    _register(ledger, root, owner)
    ledger.mark_disposed(owner)
    assert ledger.audit_payload_contracts().invalid == frozenset()


def test_contract_clear_invalidates_audit_cache_version() -> None:
    ledger, root, owner = _bound_root()
    _register(ledger, root, owner)
    registered_version = ledger.mutation_version

    ledger.clear_payload_audit_contracts()

    assert ledger.mutation_version > registered_version
    assert ledger.audit_payload_contracts().approved == frozenset()


def _assert_snapshot_has_no_authority(
    snapshot: PayloadAuditContractAudit, ledger: ResourceLedger, root: _FamilyRoot
) -> None:
    assert snapshot.approved == frozenset()
    assert snapshot.family("antihydra", ledger=ledger) == (frozenset(), frozenset())
    assert not snapshot.owns_root("antihydra", root, ledger=ledger)


def test_contract_snapshot_is_bound_to_its_ledger_and_store_version() -> None:
    ledger, root, owner = _bound_root()
    value = object()
    ledger.reserve(owner, entries=1, nodes=1)
    root.records.append(value)
    root.proposal = PayloadAuditContribution(
        approved=(PayloadAuditEntry(owner, value),)
    )
    _register(ledger, root, owner)
    snapshot = ledger.audit_payload_contracts()
    assert snapshot.family("antihydra", ledger=ledger)[0] == frozenset(
        ((owner, id(value)),)
    )
    assert snapshot.owns_root("antihydra", root, ledger=ledger)

    foreign_ledger = ResourceLedger()
    assert snapshot.family("antihydra", ledger=foreign_ledger) == (
        frozenset(),
        frozenset(),
    )
    assert not snapshot.owns_root("antihydra", root, ledger=foreign_ledger)

    ledger.note_store_mutation()
    _assert_snapshot_has_no_authority(snapshot, ledger, root)


def test_forged_contract_snapshot_cannot_approve_objects_or_roots() -> None:
    ledger, root, owner = _bound_root()
    value = object()
    ledger.reserve(owner, entries=1, nodes=1)
    root.records.append(value)
    root.proposal = PayloadAuditContribution(
        approved=(PayloadAuditEntry(owner, value),)
    )
    _register(ledger, root, owner)
    issued = ledger.audit_payload_contracts()
    forged_value = object()
    forged = PayloadAuditContractAudit(
        _approved=frozenset(((owner, id(forged_value)),)),
        _invalid=frozenset(),
        _result_ids=frozenset((id(forged_value),)),
        _by_family=(
            (
                "antihydra",
                frozenset(((owner, id(forged_value)),)),
                frozenset(),
            ),
        ),
        _roots_by_family=(("antihydra", frozenset((id(root),)), frozenset()),),
        _ledger_reference=cast(
            ReferenceType[object] | None,
            object.__getattribute__(issued, "_ledger_reference"),
        ),
        _mutation_version=cast(
            int | None, object.__getattribute__(issued, "_mutation_version")
        ),
        _registry_identity=cast(
            int | None, object.__getattribute__(issued, "_registry_identity")
        ),
    )

    assert issued.approved == frozenset(((owner, id(value)),))
    _assert_snapshot_has_no_authority(forged, ledger, root)


def test_contract_does_not_keep_closed_over_roots_alive() -> None:
    ledger, root, owner = _bound_root()
    _register(ledger, root, owner)
    del root
    gc.collect()

    assert tuple(ledger.iter_execution_roots()) == ()
    audit = ledger.audit_payload_contracts()
    assert audit.approved == frozenset()
    assert audit.roots_by_family == ()
