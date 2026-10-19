"""Independent audit of the charged field-image semantic-domain registry."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import TypeVar

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.field_image_domains import (
    FieldImageDomain,
    FieldImageDomainKey,
    FieldImageInterfaceAuthority,
    FieldImageOutputAuthority,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    FieldImageRecord,
    FieldImageSemanticKey,
    ImageRequestKey,
    RecursiveFieldImageArena,
)
from number_compiler.resources.field_image_audit_contracts import (
    RecursiveFieldImageAuditSnapshot,
)
from number_compiler.resources.ledger import ResourceLedger


def audit_field_image_domains(
    root: RecursiveFieldImageArena,
    state: RecursiveFieldImageAuditSnapshot,
    ledger: ResourceLedger,
    containers: Mapping[int, object],
) -> tuple[bool, set[int], set[tuple[int, int]]]:
    """Validate role indexes, authorities, and their retained callbacks."""
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    roots = tuple(root.ledger.iter_execution_roots())
    valid_root = (
        state.ledger is ledger
        and state.owner is root.owner
        and containers.get(state.domain_owner) is state.domains
        and bool(state.domains)
    )
    action_domains = 0
    for key, record in state.domains.items():
        valid = valid_root and type(key) is FieldImageDomainKey
        if valid:
            valid &= (
                type(key.role) is str
                and key.role in ("action", "interface", "output")
                and type(key.owner) is ArenaToken
                and type(key.kind) is str
                and bool(key.kind)
            )
        if type(record) is FieldImageDomain:
            action_domains += 1
            valid &= key == FieldImageDomainKey(
                "action",
                record.action_owner,
                record.action_kind,
            )
            valid &= (
                record.interfaces.ledger is ledger
                and callable(record.action_validate)
                and callable(record.output_validate)
                and callable(record.signature_for)
                and state.domains.get(
                    FieldImageDomainKey(
                        "interface",
                        record.interfaces.owner,
                        record.interfaces.interface_kind,
                    )
                )
                == FieldImageInterfaceAuthority(
                    record.interfaces,
                    record.signature_kind,
                )
            )
            output = state.domains.get(
                FieldImageDomainKey(
                    "output",
                    record.output_owner,
                    record.output_kind,
                )
            )
            valid &= type(output) is FieldImageOutputAuthority
            if type(output) is FieldImageOutputAuthority:
                valid &= getattr(output.validate, "__self__", None) is getattr(
                    record.output_validate, "__self__", None
                ) and getattr(output.validate, "__func__", output.validate) is getattr(
                    record.output_validate,
                    "__func__",
                    record.output_validate,
                )
            valid &= (
                record.action_authority is not None
                and any(item is record.action_authority for item in roots)
                and getattr(record.action_authority, "ledger", None) is ledger
                and getattr(record.action_validate, "__self__", None)
                is record.action_authority
                and record.signature_authority is not None
                and any(item is record.signature_authority for item in roots)
                and getattr(record.signature_authority, "ledger", None) is ledger
                and getattr(record.signature_for, "__self__", None)
                is record.signature_authority
            )
        elif type(record) is FieldImageInterfaceAuthority:
            valid &= (
                key
                == FieldImageDomainKey(
                    "interface",
                    record.arena.owner,
                    record.arena.interface_kind,
                )
                and record.arena.ledger is ledger
                and type(record.signature_kind) is str
                and bool(record.signature_kind)
            )
        elif type(record) is FieldImageOutputAuthority:
            valid &= key == FieldImageDomainKey("output", record.owner, record.kind)
            valid &= callable(record.validate)
            valid &= (
                record.authority is not None
                and any(item is record.authority for item in roots)
                and getattr(record.authority, "ledger", None) is ledger
                and getattr(record.validate, "__self__", None) is record.authority
            )
        else:
            valid = False
        if valid:
            approved.update((id(key), id(record)))
        else:
            invalid.add((state.domain_owner, id(key)))
    valid_root &= action_domains > 0 and not invalid
    if valid_root:
        approved.add(id(state.domains))
    return valid_root, approved, invalid


def audit_recursive_field_images(
    root: RecursiveFieldImageArena,
    state: RecursiveFieldImageAuditSnapshot,
    ledger: ResourceLedger,
    containers: Mapping[int, object],
) -> tuple[bool, set[int], set[tuple[int, int]]]:
    """Validate retained recursive images and both directions of their indexes."""
    stores = (
        (state.domain_owner, state.domains),
        (state.node_owner, state.nodes),
        (state.key_owner, state.keys),
        (state.binding_owner, state.bindings),
    )
    valid_root = (
        state.ledger is ledger
        and state.owner is root.owner
        and all(containers.get(owner) is store for owner, store in stores)
    )
    domains_valid, approved, invalid = audit_field_image_domains(
        root, state, ledger, containers
    )
    valid_root &= domains_valid
    valid_root &= type(state.next_id) is int and state.next_id >= 0
    for index, record in state.nodes.items():
        valid = valid_root and type(index) is int and type(record) is FieldImageRecord
        try:
            record.__post_init__()
            valid &= (
                root.resolve(FieldImageID(state.owner, state.image_kind, index))
                is record
            )
            root.resolve_interface(record.interface)
            geometry = root.geometries.resolve(record.geometry)
            valid &= geometry.spatial_level == record.level
            root.validate_output(record.output)
            if record.left is not None and record.right is not None:
                valid &= record.left.local_id < index
                valid &= record.right.local_id < index
                if valid:
                    left_record = root.resolve(record.left)
                    right_record = root.resolve(record.right)
                    valid &= left_record.level < record.level
                    valid &= right_record.level < record.level
            else:
                valid &= record.left is record.right is None
            semantic = FieldImageSemanticKey(
                record.level,
                record.left,
                record.right,
                record.interface,
                record.output,
                record.geometry,
                record.summary,
            )
            valid &= state.keys.get(semantic) == index
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        if valid:
            approved.add(id(record))
        else:
            invalid.add((state.node_owner, id(record)))
    for request, reference in state.bindings.items():
        valid = type(request) is ImageRequestKey
        try:
            root.validate_request(request)
            record = root.resolve(reference)
            valid &= (
                root.resolve_interface(record.interface).signature == request.signature
            )
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        if valid:
            approved.add(id(request))
        else:
            invalid.add((state.binding_owner, id(request)))
    for semantic, index in state.keys.items():
        valid = type(semantic) is FieldImageSemanticKey and type(index) is int
        valid &= index in state.nodes
        if valid:
            record = state.nodes[index]
            expected = FieldImageSemanticKey(
                record.level,
                record.left,
                record.right,
                record.interface,
                record.output,
                record.geometry,
                record.summary,
            )
            valid &= semantic == expected
        if valid:
            approved.add(id(semantic))
        else:
            invalid.add((state.key_owner, id(semantic)))
    image_owners = {state.node_owner, state.key_owner, state.binding_owner}
    if valid_root and not any(owner in image_owners for owner, _ in invalid):
        approved.update(id(store) for _, store in stores)
    return valid_root, approved, invalid


__all__ = ["audit_field_image_domains", "audit_recursive_field_images"]


_Record = TypeVar("_Record")
_Handle = TypeVar("_Handle")


def indexed_record_matches(
    handle: _Handle,
    resolve: Callable[[_Handle], _Record],
    keys: Mapping[_Record, int],
    record: _Record,
    local_id: int,
) -> bool:
    """Audit both directions of an arena index without equating distinct records."""
    return (resolve(handle) is record) & (keys.get(record) == local_id)


def admit_payload_root(
    valid: bool, invalid: set[tuple[int, int]], owner: int, root: object
) -> bool:
    """Record a failed root before suppressing traversal of its untrusted stores."""
    if not valid:
        invalid.add((owner, id(root)))
    return valid
