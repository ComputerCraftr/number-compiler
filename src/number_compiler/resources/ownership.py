"""Independent retained-store audit from execution objects, not memo callbacks."""

from __future__ import annotations

from collections.abc import (
    Iterable,
    Mapping,
    MutableMapping,
    MutableSequence,
    MutableSet,
)
from dataclasses import dataclass
from enum import Enum
from functools import cached_property, partial
from gc import get_referents
from types import (
    BuiltinFunctionType,
    CoroutineType,
    FrameType,
    FunctionType,
    GeneratorType,
    MappingProxyType,
    MethodType,
    ModuleType,
)
from typing import TypeGuard, cast
from weakref import ReferenceType

from number_compiler.arithmetic.contracts.input_validation import (
    is_object_list_instance,
    is_object_tuple,
    object_mapping,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.stores import LedgerDict, LedgerList


@dataclass(frozen=True, slots=True)
class OwnershipViolation:
    path: str
    type_name: str
    reason: str


@dataclass(frozen=True, slots=True)
class OwnershipAudit:
    roots: int
    observed_mutable_containers: int
    violations: tuple[OwnershipViolation, ...]

    @property
    def unregistered_containers(self) -> int:
        return len(self.violations)


def _as_untrusted_object(value: object) -> object:
    """Drop container-specific generic types before traversing erased objects."""
    return value


def _is_object_reference(value: object) -> TypeGuard[ReferenceType[object]]:
    """Narrow weak references to their read-only object-target view."""
    return isinstance(value, ReferenceType)


def _mutable(value: object) -> bool:
    return isinstance(value, (MutableMapping, MutableSequence, MutableSet))


def audit_execution_ownership(
    ledger: ResourceLedger,
    *,
    fresh: bool = True,
) -> OwnershipAudit:
    """Walk actual fields, slots, nested values and function closures iteratively.

    Instance dictionaries are attribute plumbing, not memo payloads: their
    values are traversed. Only exact bookkeeping container identities are
    exempt from ownership classification; their values and callbacks are still
    traversed. A different ledger in the execution graph is a violation.
    Immutable source/kernel tuples are followed, including their nested values.
    """
    roots = tuple(ledger.iter_execution_roots())
    root_signature = ledger.audit_root_signature() if not fresh else None
    # Public metric collection uses the ledger mutation epoch and requests a
    # cached audit. Explicit adversarial audits remain fresh by default so an
    # injected ordinary root attribute cannot hide behind a retained result.
    if not fresh:
        cached = ledger.cached_ownership_audit(root_signature)
        if type(cached) is OwnershipAudit:
            return cached
    elif not roots:
        cached = ledger.cached_ownership_audit()
        if type(cached) is OwnershipAudit:
            return cached
    audit_version = ledger.mutation_version
    registered: dict[int, list[int]] = {}
    for owner, container in ledger.iter_containers():
        registered.setdefault(id(container), []).append(owner)
    statuses = {item.owner: item.disposed for item in ledger.inventory()}
    bookkeeping = set(ledger.ownership_audit_identities())
    violations: list[OwnershipViolation] = []
    seen: set[int] = set()
    layouts: dict[
        type[object], tuple[tuple[str, ...], tuple[tuple[str, object], ...]]
    ] = {}
    mutable_count = 0
    stack: list[tuple[object, str]] = [
        (ledger, "ResourceLedger"),
        *((root, type(root).__name__) for root in roots),
    ]
    while stack:
        audit_frame = stack.pop()
        value = audit_frame[0]
        path = audit_frame[1]
        untrusted = _as_untrusted_object(value)
        value_type: type[object] = type(untrusted)
        type_name = value_type.__name__
        if value is None or isinstance(
            value, (str, int, float, complex, bytes, Enum, type, ModuleType)
        ):
            continue
        identity = id(value)
        if identity in seen:
            continue
        seen.add(identity)
        if isinstance(value, ResourceLedger) and value is not ledger:
            violations.append(
                OwnershipViolation(
                    path, type(value).__name__, "foreign ledger in execution graph"
                )
            )
            continue
        verified_store = type(value) in (
            LedgerDict,
            LedgerList,
        ) and ledger.is_factory_container(value)
        if (
            _mutable(value)
            and type(value) is not OwnedMemo
            and identity not in bookkeeping
        ):
            mutable_count += 1
            owners = registered.get(identity, [])
            reason = ""
            if not verified_store or not isinstance(value, (LedgerDict, LedgerList)):
                reason = "retained mutable store was not created by the ledger factory"
            elif (
                len(owners) != 1
                or value.ledger is not ledger
                or owners[0] != value.owner
            ):
                reason = "factory store lacks exactly one matching owner"
            elif statuses[owners[0]] and bool(untrusted):
                reason = "disposed owner still retains mutable payloads"
            if reason:
                verified_store = False
                violations.append(OwnershipViolation(path, type_name, reason))
        if isinstance(value, cached_property) or (
            callable(audit_frame[0])
            and hasattr(audit_frame[0], "cache_info")
            and hasattr(audit_frame[0], "cache_clear")
        ):
            violations.append(
                OwnershipViolation(
                    path,
                    type_name,
                    "retained callable contains an unowned runtime cache",
                )
            )
        if isinstance(value, MappingProxyType):
            # A read-only view does not freeze its mutable backing dictionary.
            # CPython exposes the actual referent; require normal factory
            # provenance for that store just as for a direct field reference.
            backing_value: object = get_referents(untrusted)
            backing = backing_value if is_object_list_instance(backing_value) else None
            if (
                backing is None
                or len(backing) != 1
                or object_mapping(backing[0]) is None
            ):
                violations.append(
                    OwnershipViolation(
                        path,
                        type_name,
                        "cannot verify mapping proxy backing ownership",
                    )
                )
            else:
                stack.append((backing[0], path + ".backing"))
        mapping: Mapping[object, object] | None
        if isinstance(value, Mapping):
            mapping = cast(Mapping[object, object], value)
        else:
            mapping = None
        if mapping is not None and value_type is not OwnedMemo:
            for position, (key, child) in enumerate(audit_mapping_items(mapping)):
                stack.extend(
                    (
                        (key, f"{path}.key[{position}]"),
                        (child, f"{path}.value[{position}]"),
                    )
                )
        elif isinstance(value, (tuple, MutableSequence, MutableSet, frozenset)):
            children = cast(Iterable[object], value)
            stack.extend(
                (child, f"{path}[{position}]")
                for position, child in enumerate(children)
            )
        reference_candidate = audit_frame[0]
        if _is_object_reference(reference_candidate):
            referent = reference_candidate()
            stack.append((referent, path + ".referent"))
        if isinstance(value, partial):
            stack.extend(
                (
                    (value.func, path + ".func"),
                    (value.args, path + ".args"),
                    (value.keywords, path + ".keywords"),
                )
            )
        if isinstance(value, BuiltinFunctionType):
            stack.append((value.__self__, path + ".__self__"))
        if isinstance(value, GeneratorType):
            stack.append((value.gi_frame, path + ".frame"))
        if isinstance(value, CoroutineType):
            stack.append((value.cr_frame, path + ".frame"))
        if isinstance(value, FrameType):
            stack.extend(
                (child, path + ".local." + name)
                for name, child in value.f_locals.items()
            )
        if isinstance(value, MethodType):
            stack.extend(
                (
                    (value.__self__, path + ".__self__"),
                    (value.__func__, path + ".__func__"),
                )
            )
        if isinstance(value, FunctionType):
            for position, cell in enumerate(value.__closure__ or ()):
                try:
                    child = cell.cell_contents
                except ValueError:
                    continue
                stack.append((child, f"{path}.closure[{position}]"))
            stack.append((value.__defaults__, path + ".defaults"))
            if value.__kwdefaults__:
                stack.extend(
                    (child, path + ".kwdefault." + name)
                    for name, child in value.__kwdefaults__.items()
                )
            for name in value.__code__.co_names:
                child = value.__globals__.get(name)
                if _mutable(child):
                    stack.append((child, path + ".global." + name))
        try:
            attribute_value: object = vars(value)
        except TypeError:
            attribute_value = {}
        attributes = object_mapping(attribute_value)
        if attributes is not None:
            for attribute_name, child in attributes.items():
                if not (
                    verified_store
                    and attribute_name == "_data"
                    and isinstance(child, (dict, list))
                ) and not (
                    attribute_name == "__annotations__" and isinstance(child, dict)
                ):
                    label = (
                        attribute_name
                        if type(attribute_name) is str
                        else "<non-string attribute>"
                    )
                    stack.append((child, path + "." + label))
        layout = layouts.get(value_type)
        if layout is None:
            slot_names: list[str] = []
            class_children: list[tuple[str, object]] = []
            for cls in value_type.__mro__:
                slots_value: object = cls.__dict__.get("__slots__", ())
                slots = slots_value
                if isinstance(slots, str):
                    slots = (slots,)
                elif not is_object_tuple(slots):
                    slots = ()
                for slot_name in slots:
                    if type(slot_name) is not str:
                        continue
                    if slot_name in ("__dict__", "__weakref__"):
                        continue
                    if slot_name.startswith("__") and not slot_name.endswith("__"):
                        slot_name = "_" + cls.__name__.lstrip("_") + slot_name
                    slot_names.append(slot_name)
                namespace_value: object = cls.__dict__
                namespace = object_mapping(namespace_value)
                if namespace is None:
                    continue
                for class_name, class_child in namespace.items():
                    if type(class_name) is not str:
                        continue
                    class_child_value: object = class_child
                    if not class_name.startswith("__") and (
                        _mutable(class_child)
                        or isinstance(class_child, cached_property)
                        or callable(class_child)
                        and hasattr(class_child, "cache_info")
                        and hasattr(class_child, "cache_clear")
                    ):
                        class_children.append((class_name, class_child_value))
            layout = tuple(slot_names), tuple(class_children)
            layouts[value_type] = layout
        cached_slot_names, cached_class_children = layout
        for name in cached_slot_names:
            try:
                slot_box: tuple[object, ...] = (getattr(untrusted, name),)
                slot_value = slot_box[0]
            except AttributeError:
                continue
            if (
                verified_store
                and name == "_data"
                and isinstance(slot_value, (dict, list))
            ):
                continue
            stack.append((slot_value, path + "." + name))
        stack.extend(
            (child, path + ".class." + name) for name, child in cached_class_children
        )
    result = OwnershipAudit(len(roots), mutable_count, tuple(violations))
    if not fresh or not roots:
        ledger.cache_ownership_audit(audit_version, result, root_signature)
    return result
