"""Compatibility view over family-owned reverse/add audit contracts."""

from __future__ import annotations

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit


def audit_reverse_field_action_root(
    root: object,
    ledger: ResourceLedger,
    containers: dict[int, object],
    contracts: PayloadAuditContractAudit | None = None,
) -> tuple[set[int], set[tuple[int, int]]]:
    """Return the already-audited reverse/add family partition.

    The historical arguments remain for callers during migration; exact root
    and store authority is established when the family registers its contract.
    """
    del root, containers
    audit = ledger.audit_payload_contracts() if contracts is None else contracts
    approved, invalid = audit.family("reverse_add")
    return {identity for _, identity in approved}, set(invalid)


__all__ = ["audit_reverse_field_action_root"]
