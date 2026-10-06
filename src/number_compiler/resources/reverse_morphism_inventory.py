"""Shared adapter for reverse-family contract audit results."""

from __future__ import annotations

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit


def audit_reverse_morphisms(
    ledger: object,
    roots: tuple[object, ...],
    contracts: PayloadAuditContractAudit | None = None,
) -> tuple[set[int], set[tuple[int, int]]]:
    """Return already-validated reverse-family approvals without rescanning."""
    if not isinstance(ledger, ResourceLedger):
        return set(), set()
    del roots
    if contracts is None:
        contracts = ledger.audit_payload_contracts()
    approved, invalid = contracts.family("reverse_add", ledger=ledger)
    return {identity for _, identity in approved}, set(invalid)


__all__ = ["audit_reverse_morphisms"]
