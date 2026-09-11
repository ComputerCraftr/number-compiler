"""Independent audit of the charged field-image semantic-domain registry."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.field_image_domains import (
    _DomainLookupKey,
    _FieldImageDomain,
    _InterfaceAuthority,
    _OutputAuthority,
)
from number_compiler.hashlife.execution.field_images import RecursiveFieldImageArena


def audit_field_image_domains(
    root: RecursiveFieldImageArena,
    ledger: object,
    containers: Mapping[int, object],
) -> tuple[bool, set[int], set[tuple[int, int]]]:
    """Validate role indexes, authorities, and their retained callbacks."""
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    roots = tuple(root.ledger.iter_execution_roots())
    valid_root = (
        root.ledger is ledger
        and containers.get(root._domain_owner) is root._domains
        and bool(root._domains)
    )
    action_domains = 0
    for key, record in root._domains.items():
        valid = valid_root and type(key) is _DomainLookupKey
        if valid:
            valid &= (
                type(key.role) is str
                and key.role in ("action", "interface", "output")
                and type(key.owner) is ArenaToken
                and type(key.kind) is str
                and bool(key.kind)
            )
        if type(record) is _FieldImageDomain:
            action_domains += 1
            valid &= key == _DomainLookupKey(
                "action",
                record.action_owner,
                record.action_kind,
            )
            valid &= (
                record.interfaces.ledger is ledger
                and callable(record.action_validate)
                and callable(record.output_validate)
                and callable(record.signature_for)
                and root._domains.get(
                    _DomainLookupKey(
                        "interface",
                        record.interfaces.owner,
                        record.interfaces.interface_kind,
                    )
                )
                == _InterfaceAuthority(
                    record.interfaces,
                    record.signature_kind,
                )
            )
            output = root._domains.get(
                _DomainLookupKey(
                    "output",
                    record.output_owner,
                    record.output_kind,
                )
            )
            valid &= type(output) is _OutputAuthority
            if type(output) is _OutputAuthority:
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
        elif type(record) is _InterfaceAuthority:
            valid &= (
                key
                == _DomainLookupKey(
                    "interface",
                    record.arena.owner,
                    record.arena.interface_kind,
                )
                and record.arena.ledger is ledger
                and type(record.signature_kind) is str
                and bool(record.signature_kind)
            )
        elif type(record) is _OutputAuthority:
            valid &= key == _DomainLookupKey("output", record.owner, record.kind)
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
            invalid.add((root._domain_owner, id(key)))
    valid_root &= action_domains > 0 and not invalid
    if valid_root:
        approved.add(id(root._domains))
    return valid_root, approved, invalid


__all__ = ["audit_field_image_domains"]
