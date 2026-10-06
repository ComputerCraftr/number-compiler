"""Compatibility view over reverse/add family-owned audit contracts."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit


@dataclass(frozen=True, slots=True)
class ReverseSourcePayloadAudit:
    """Owner-qualified reverse/add evidence with a legacy identity view."""

    approved: frozenset[int]
    recognized: frozenset[int]
    invalid: frozenset[tuple[int, int]]
    owner_approved: frozenset[tuple[int, int]] = frozenset()

    def recognizes(self, value: object) -> bool:
        return id(value) in self.recognized

    def valid(self, value: object, *, owner: int | None = None) -> bool:
        if owner is not None:
            return (owner, id(value)) in self.owner_approved
        return id(value) in self.approved


def audit_reverse_source_payloads(
    ledger: ResourceLedger,
    roots: tuple[object, ...],
    containers: Mapping[int, object],
    contracts: PayloadAuditContractAudit | None = None,
) -> ReverseSourcePayloadAudit:
    """Read the existing family partition without rewalking sequence stores."""
    del roots, containers
    audit = ledger.audit_payload_contracts() if contracts is None else contracts
    approved_pairs, invalid = audit.family("reverse_add")
    root_ids = frozenset(
        identity
        for family, valid_roots, invalid_roots in audit.roots_by_family
        if family == "reverse_add"
        for identity in valid_roots - invalid_roots
    )
    approved = frozenset(identity for _, identity in approved_pairs) | root_ids
    recognized = approved | frozenset(identity for _, identity in invalid)
    return ReverseSourcePayloadAudit(approved, recognized, invalid, approved_pairs)


__all__ = ["ReverseSourcePayloadAudit", "audit_reverse_source_payloads"]
