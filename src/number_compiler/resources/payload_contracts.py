"""Per-ledger contracts for family-owned retained-payload validators."""

from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from inspect import getattr_static
from types import FunctionType, MemberDescriptorType
from typing import TYPE_CHECKING, cast
from weakref import ReferenceType, ref

from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.payload_containers import audit_mapping_items

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger


def _contract_semantic_component(
    value: object,
    *,
    owner: int,
    approved: frozenset[tuple[int, int]],
    owned_semantic_members: frozenset[tuple[int, int]],
    semantic: Callable[..., bool],
) -> bool:
    """Consume an owner-qualified approval within the current audit snapshot."""
    identity = owner, id(value)
    return (
        identity in approved
        or identity in owned_semantic_members
        or semantic(value, owner=owner)
    )


@dataclass(frozen=True, slots=True)
class PayloadAuditStoreBinding:
    """One exact family-owned root attribute and its ledger account."""

    owner: int
    attribute: str
    role: str


@dataclass(frozen=True, slots=True)
class PayloadAuditEntry:
    """A concrete object proposed by an owner audit, never a caller-supplied ID."""

    owner: int
    value: object


@dataclass(frozen=True, slots=True)
class PayloadAuditContribution:
    """Concrete direct-store members validated or rejected by one owner audit."""

    approved: tuple[PayloadAuditEntry, ...] = ()
    invalid: tuple[PayloadAuditEntry, ...] = ()


@dataclass(frozen=True, slots=True)
class PayloadAuditContractAudit:
    """Validated, owner-qualified results from all live family contracts."""

    _approved: frozenset[tuple[int, int]]
    _invalid: frozenset[tuple[int, int]]
    _by_family: tuple[
        tuple[str, frozenset[tuple[int, int]], frozenset[tuple[int, int]]], ...
    ] = ()
    _roots_by_family: tuple[tuple[str, frozenset[int], frozenset[int]], ...] = ()
    _ledger_reference: ReferenceType[object] | None = None
    _mutation_version: int | None = None
    _registry_identity: int | None = None

    def _is_current(self, ledger: object | None = None) -> bool:
        reference = self._ledger_reference
        if reference is None:
            return False
        owner = reference()
        if owner is None or (ledger is not None and owner is not ledger):
            return False
        from number_compiler.resources.ledger import ResourceLedger

        return (
            type(owner) is ResourceLedger
            and owner._payload_audit_snapshot is self
            and owner.mutation_version == self._mutation_version
            and id(owner._payload_audit_contracts) == self._registry_identity
        )

    def is_current_for(self, ledger: ResourceLedger) -> bool:
        return self._is_current(ledger)

    @property
    def approved(self) -> frozenset[tuple[int, int]]:
        return self._approved if self._is_current() else frozenset()

    @property
    def invalid(self) -> frozenset[tuple[int, int]]:
        return self._invalid if self._is_current() else frozenset()

    @property
    def by_family(
        self,
    ) -> tuple[tuple[str, frozenset[tuple[int, int]], frozenset[tuple[int, int]]], ...]:
        return self._by_family if self._is_current() else ()

    @property
    def roots_by_family(self) -> tuple[tuple[str, frozenset[int], frozenset[int]], ...]:
        return self._roots_by_family if self._is_current() else ()

    def family(
        self, name: str, *, ledger: ResourceLedger | None = None
    ) -> tuple[frozenset[tuple[int, int]], frozenset[tuple[int, int]]]:
        if not self._is_current(ledger):
            return frozenset(), frozenset()
        for family, approved, invalid in self._by_family:
            if family == name:
                return (
                    frozenset(item for item in approved if item not in invalid),
                    invalid,
                )
        return frozenset(), frozenset()

    def owns_root(
        self,
        family: str,
        root: object,
        *,
        ledger: ResourceLedger | None = None,
    ) -> bool:
        """Whether this snapshot accepted a live contract for the exact root."""
        if not self._is_current(ledger):
            return False
        identity = id(root)
        return any(
            name == family and identity in valid and identity not in invalid
            for name, valid, invalid in self._roots_by_family
        )


@dataclass(frozen=True, slots=True)
class _PayloadAuditBinding:
    family: str
    root_identity: int
    root_type: type[object]
    root_reference: ReferenceType[object]
    stores: tuple[tuple[int, str, object, str], ...]
    validator: Callable[[object, object], PayloadAuditContribution]
    dependencies: tuple[tuple[int, str, ReferenceType[object]], ...]


def _drop_root_contracts(ledger: ResourceLedger, identity: int) -> None:
    for key, binding in tuple(ledger._payload_audit_contracts.items()):
        if binding.root_identity == identity:
            ledger._payload_audit_contracts.pop(key, None)


def _drop_owner_contracts(ledger: ResourceLedger, owner: int) -> None:
    for key, binding in tuple(ledger._payload_audit_contracts.items()):
        if any(bound_owner == owner for bound_owner, _, _, _ in binding.stores):
            ledger._payload_audit_contracts.pop(key, None)


def register_payload_audit_contract(
    ledger: ResourceLedger,
    root: object,
    family: str,
    stores: tuple[PayloadAuditStoreBinding, ...],
    validator: Callable[[object, object], PayloadAuditContribution],
    *,
    dependencies: tuple[object, ...] = (),
) -> None:
    """Bind a family validator to exact stores and optional contracted child roots.

    Dependencies are exact live roots with their own family contracts. Their
    validators must remain clean for this root's contract to be accepted.
    """
    if type(family) is not str or not family.isidentifier():
        raise ValueError("payload audit family must be an identifier")
    module_prefix = f"number_compiler.sequences.{family}."
    root_module = type(root).__module__.split(".")
    if len(root_module) < 4 or root_module[:3] != [
        "number_compiler",
        "sequences",
        family,
    ]:
        raise ValueError("payload audit root is not owned by the named family")
    if (
        not isinstance(validator, FunctionType)
        or validator.__module__ is None
        or not validator.__module__.startswith(module_prefix)
        or validator.__name__ == "<lambda>"
        or validator.__closure__ is not None
        or validator.__defaults__ is not None
        or validator.__kwdefaults__ is not None
        or validator.__dict__
    ):
        raise ValueError(
            "payload audit validators must be closure-free module functions"
        )
    if type(stores) is not tuple or not stores:
        raise TypeError("payload audit contracts require exact owned stores")
    if type(dependencies) is not tuple:
        raise TypeError("payload audit dependencies must be an exact tuple")
    roots = ledger._execution_roots.get(id(root))
    if roots is None or roots() is not root:
        raise ValueError("payload audit root must already be registered")
    for ledger_attribute in ("_ledger", "ledger"):
        root_ledger = getattr_static(root, ledger_attribute, None)
        if isinstance(root_ledger, MemberDescriptorType):
            root_ledger = root_ledger.__get__(root, type(root))
        if root_ledger is None or isinstance(root_ledger, property):
            continue
        if root_ledger is not ledger:
            raise ValueError("payload audit root belongs to another ledger")
        break

    bound: list[tuple[int, str, object, str]] = []
    owners: set[int] = set()
    containers: set[int] = set()
    for store_binding in stores:
        if type(store_binding) is not PayloadAuditStoreBinding:
            raise TypeError("payload audit store bindings must be exact records")
        owner, attribute, role = (
            store_binding.owner,
            store_binding.attribute,
            store_binding.role,
        )
        if (
            type(owner) is not int
            or type(attribute) is not str
            or not attribute
            or type(role) is not str
            or not role
        ):
            raise TypeError("payload audit store binding has invalid fields")
        if owner in owners:
            raise ValueError("payload audit owner bindings must be unique")
        account = ledger._account(owner)
        container = account.container
        if (
            account.disposed
            or container is None
            or account.role != role
            or getattr(root, attribute, None) is not container
            or id(container) in containers
        ):
            raise ValueError("payload audit store is not the exact live owner")
        owners.add(owner)
        containers.add(id(container))
        bound.append((owner, attribute, container, role))

    key = (id(root), family)
    dependency_bindings: list[tuple[int, str, ReferenceType[object]]] = []
    dependency_ids: set[int] = set()
    dependency_keys: list[tuple[int, str]] = []
    for dependency in dependencies:
        identity = id(dependency)
        reference = ledger._execution_roots.get(identity)
        module_parts = type(dependency).__module__.split(".")
        dependency_family = (
            module_parts[2]
            if len(module_parts) >= 4
            and module_parts[:2] == ["number_compiler", "sequences"]
            else ""
        )
        dependency_key = (identity, dependency_family)
        child = ledger._payload_audit_contracts.get(dependency_key)
        if (
            dependency is root
            or identity in dependency_ids
            or reference is None
            or reference() is not dependency
            or child is None
            or child.root_reference() is not dependency
        ):
            raise ValueError(
                "payload audit dependency must be an exact live contracted root"
            )
        dependency_ids.add(identity)
        dependency_keys.append(dependency_key)
        dependency_bindings.append((identity, dependency_family, ref(dependency)))

    # Dependencies must remain a DAG so audit invalidation can propagate in one
    # linear worklist pass without rescanning family stores.
    pending = list(dependency_keys)
    visited: set[tuple[int, str]] = set()
    while pending:
        dependency_key = pending.pop()
        if dependency_key == key:
            raise ValueError("payload audit dependency cycle")
        if dependency_key in visited:
            continue
        visited.add(dependency_key)
        child = ledger._payload_audit_contracts.get(dependency_key)
        if child is not None:
            pending.extend(
                (child_identity, child_family)
                for child_identity, child_family, _ in child.dependencies
            )

    current = ledger._payload_audit_contracts.get(key)
    if current is not None:
        if (
            current.root_reference() is root
            and current.root_type is type(root)
            and len(current.stores) == len(bound)
            and all(
                old_owner == new_owner
                and old_attribute == new_attribute
                and old_container is new_container
                and old_role == new_role
                for (
                    old_owner,
                    old_attribute,
                    old_container,
                    old_role,
                ), (
                    new_owner,
                    new_attribute,
                    new_container,
                    new_role,
                ) in zip(current.stores, bound, strict=True)
            )
            and current.validator is validator
            and len(current.dependencies) == len(dependency_bindings)
            and all(
                old_identity == new_identity
                and old_family == new_family
                and old_reference() is new_reference()
                for (old_identity, old_family, old_reference), (
                    new_identity,
                    new_family,
                    new_reference,
                ) in zip(current.dependencies, dependency_bindings, strict=True)
            )
        ):
            return
        raise ValueError("replace an existing payload audit contract explicitly")
    ledger._payload_audit_contracts[key] = _PayloadAuditBinding(
        family,
        id(root),
        type(root),
        ref(root),
        tuple(bound),
        validator,
        tuple(dependency_bindings),
    )
    ledger.note_store_mutation()


def remove_payload_audit_contract(
    ledger: ResourceLedger, root: object, family: str | None = None
) -> None:
    """Remove one root's contract(s), invalidating cached audit evidence."""
    if family is not None and (type(family) is not str or not family):
        raise ValueError("payload audit family must be nonempty")
    removed = False
    for key, binding in tuple(ledger._payload_audit_contracts.items()):
        if (
            binding.root_identity == id(root)
            and binding.root_reference() is root
            and (family is None or key[1] == family)
        ):
            ledger._payload_audit_contracts.pop(key, None)
            removed = True
    if removed:
        ledger.note_store_mutation()


def clear_payload_audit_contracts(ledger: ResourceLedger) -> None:
    """Clear family validators when an execution workspace is reset."""
    if ledger._payload_audit_contracts:
        ledger._payload_audit_contracts.clear()
        ledger.note_store_mutation()


def _store_identity_index(
    ledger: ResourceLedger, container: object
) -> dict[int, object]:
    """Index direct payloads, including the shared memo accounting envelope."""
    from number_compiler.resources.ledger import _DynamicMemoValue

    values: dict[int, object] = {}
    if isinstance(container, Mapping):
        for key, item in audit_mapping_items(container):
            values[id(key)] = key
            values[id(item)] = item
            ledger.bump(_resources_keys.PAYLOAD_AUDIT_CONTRACT_MEMBER_VISITS, 2)
            # This is an accounting envelope, not another semantic container.
            # Do not recursively approve arbitrary nested records or subclasses.
            if type(item) is _DynamicMemoValue:
                values[id(item.value)] = item.value
                ledger.bump(_resources_keys.PAYLOAD_AUDIT_CONTRACT_MEMBER_VISITS)
    elif isinstance(container, Sequence) and not isinstance(
        container, (str, bytes, bytearray)
    ):
        for item in container:
            values[id(item)] = item
            ledger.bump(_resources_keys.PAYLOAD_AUDIT_CONTRACT_MEMBER_VISITS)
    return values


def audit_payload_contracts(ledger: ResourceLedger) -> PayloadAuditContractAudit:
    """Run contracts and constrain approvals to direct members of live stores.

    Roots and stores may be identified as invalid, but a validator cannot
    approve an entire root or storage object as a shortcut around its contents.
    """
    audit_version = ledger.mutation_version
    approved: set[tuple[int, int]] = set()
    invalid: set[tuple[int, int]] = set()
    approved_by_family: dict[str, set[tuple[int, int]]] = {}
    invalid_by_family: dict[str, set[tuple[int, int]]] = {}
    valid_roots_by_family: dict[str, set[int]] = {}
    invalid_roots_by_family: dict[str, set[int]] = {}
    live_roots = {id(root): root for root in ledger.iter_execution_roots()}
    results: list[tuple[_PayloadAuditBinding, list[tuple[str, PayloadAuditEntry]]]] = []
    invalid_contracts: set[tuple[int, str]] = set()
    contract_keys = set(ledger._payload_audit_contracts)
    for key, binding in tuple(ledger._payload_audit_contracts.items()):
        root = binding.root_reference()
        anchor_owner = binding.stores[0][0]
        root_invalid = (anchor_owner, binding.root_identity)
        valid_roots_by_family.setdefault(binding.family, set())
        invalid_roots_by_family.setdefault(binding.family, set())

        def reject_contract(
            family_name: str = binding.family,
            invalid_pair: tuple[int, int] = root_invalid,
            root_identity: int = binding.root_identity,
            contract_key: tuple[int, str] = key,
        ) -> None:
            invalid_contracts.add(contract_key)
            invalid.add(invalid_pair)
            invalid_by_family.setdefault(family_name, set()).add(invalid_pair)
            invalid_roots_by_family[family_name].add(root_identity)

        if (
            root is None
            or live_roots.get(binding.root_identity) is not root
            or type(root) is not binding.root_type
            or key != (id(root), binding.family)
        ):
            reject_contract()
            continue
        bound: dict[int, object] = {}
        bound_by_identity: dict[int, object] = {}
        indexes: dict[int, dict[int, object]] = {}
        stores_valid = True
        for owner, attribute, container, role in binding.stores:
            account = ledger._account(owner)
            if (
                account.disposed
                or account.container is not container
                or account.role != role
                or getattr(root, attribute, None) is not container
            ):
                stores_valid = False
                break
            bound[owner] = container
            bound_by_identity[id(container)] = container
            try:
                indexes[owner] = _store_identity_index(ledger, container)
            except (
                ArithmeticError,
                AttributeError,
                IndexError,
                KeyError,
                RuntimeError,
                TypeError,
                ValueError,
            ):
                stores_valid = False
                break
        if not stores_valid:
            reject_contract()
            continue
        try:
            result = binding.validator(ledger, root)
            if type(result) is not PayloadAuditContribution:
                raise TypeError("family validator returned an untyped result")
            if type(result.approved) is not tuple or type(result.invalid) is not tuple:
                raise TypeError("family validator returned mutable or unknown rows")
            rows: list[tuple[str, PayloadAuditEntry]] = []
            for group, entries in (
                ("approved", result.approved),
                ("invalid", result.invalid),
            ):
                for entry in entries:
                    if type(entry) is not PayloadAuditEntry:
                        raise TypeError("family validator returned an unchecked ID")
                    owner = entry.owner
                    if type(owner) is not int or owner not in bound:
                        raise ValueError("family validator escaped its owned stores")
                    is_member = (
                        id(entry.value) in indexes[owner]
                        and indexes[owner][id(entry.value)] is entry.value
                    )
                    is_bound_target = (
                        id(entry.value) in bound_by_identity
                        and bound_by_identity[id(entry.value)] is entry.value
                    )
                    is_audit_target = entry.value is root or entry.value is bound[owner]
                    if (is_bound_target or entry.value is root) and group != "invalid":
                        raise ValueError(
                            "family validator cannot approve a root or bound store"
                        )
                    if not is_member and not (group == "invalid" and is_audit_target):
                        raise ValueError(
                            "family validator returned an object outside its store"
                        )
                    rows.append((group, entry))
        except (
            ArithmeticError,
            AttributeError,
            IndexError,
            KeyError,
            RuntimeError,
            TypeError,
            ValueError,
        ):
            reject_contract()
            continue
        contract_has_invalid = any(group == "invalid" for group, _ in rows)
        if contract_has_invalid:
            invalid_roots_by_family[binding.family].add(binding.root_identity)
            invalid_contracts.add(key)
        results.append((binding, rows))

    invalid_roots = {
        binding.root_identity
        for key, binding in ledger._payload_audit_contracts.items()
        if key in invalid_contracts
    }
    dependency_parents: dict[int, set[int]] = {}
    dependency_tainted_roots: set[int] = set()
    for binding in ledger._payload_audit_contracts.values():
        for identity, family, reference in binding.dependencies:
            ledger.bump(_resources_keys.PAYLOAD_AUDIT_CONTRACT_DEPENDENCY_VISITS)
            dependency_root = reference()
            dependency_key = (identity, family)
            dependency_binding = ledger._payload_audit_contracts.get(dependency_key)
            if (
                dependency_root is None
                or live_roots.get(identity) is not dependency_root
                or dependency_key not in contract_keys
                or dependency_binding is None
                or dependency_binding.root_reference() is not dependency_root
            ):
                dependency_tainted_roots.add(binding.root_identity)
                continue
            dependency_parents.setdefault(identity, set()).add(binding.root_identity)
    pending_invalid = list(invalid_roots | dependency_tainted_roots)
    tainted_seen: set[int] = set()
    while pending_invalid:
        failed = pending_invalid.pop()
        if failed in tainted_seen:
            continue
        tainted_seen.add(failed)
        for parent_identity in dependency_parents.get(failed, ()):
            if parent_identity not in dependency_tainted_roots:
                dependency_tainted_roots.add(parent_identity)
                pending_invalid.append(parent_identity)

    for binding, rows in results:
        root_identity = binding.root_identity
        if root_identity in invalid_roots or root_identity in dependency_tainted_roots:
            invalid_roots_by_family.setdefault(binding.family, set()).add(root_identity)
            if root_identity in dependency_tainted_roots:
                anchor_owner = binding.stores[0][0]
                root_invalid = (anchor_owner, root_identity)
                invalid.add(root_invalid)
                invalid_by_family.setdefault(binding.family, set()).add(root_invalid)
        else:
            valid_roots_by_family.setdefault(binding.family, set()).add(root_identity)
        for group, entry in rows:
            pair = (entry.owner, id(entry.value))
            if group == "approved":
                if root_identity not in dependency_tainted_roots:
                    approved.add(pair)
                    approved_by_family.setdefault(binding.family, set()).add(pair)
            else:
                invalid.add(pair)
                invalid_by_family.setdefault(binding.family, set()).add(pair)
    if invalid:
        approved.difference_update(invalid)
    by_family = []
    for family in sorted(approved_by_family.keys() | invalid_by_family.keys()):
        family_approved = approved_by_family.get(family, set())
        family_invalid = invalid_by_family.get(family, set())
        by_family.append(
            (
                family,
                frozenset(
                    item for item in family_approved if item not in family_invalid
                ),
                frozenset(family_invalid),
            )
        )
    roots_by_family = tuple(
        (
            family,
            frozenset(valid_roots_by_family.get(family, set())),
            frozenset(invalid_roots_by_family.get(family, set())),
        )
        for family in sorted(
            valid_roots_by_family.keys() | invalid_roots_by_family.keys()
        )
    )
    if ledger.mutation_version != audit_version:
        raise RuntimeError("resource stores changed during payload contract audit")
    snapshot = PayloadAuditContractAudit(
        _approved=frozenset(approved),
        _invalid=frozenset(invalid),
        _by_family=tuple(by_family),
        _roots_by_family=roots_by_family,
        _ledger_reference=cast(ReferenceType[object], ref(ledger)),
        _mutation_version=audit_version,
        _registry_identity=id(ledger._payload_audit_contracts),
    )
    ledger._payload_audit_snapshot = snapshot
    return snapshot


__all__ = [
    "PayloadAuditContractAudit",
    "PayloadAuditContribution",
    "PayloadAuditEntry",
    "PayloadAuditStoreBinding",
    "audit_payload_contracts",
    "clear_payload_audit_contracts",
    "register_payload_audit_contract",
    "remove_payload_audit_contract",
]
