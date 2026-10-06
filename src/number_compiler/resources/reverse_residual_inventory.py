"""Shared adapter for reverse-family contract audit results."""

from __future__ import annotations

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit


def audit_reverse_residuals(
    ledger: object,
    roots: tuple[object, ...],
    contracts: PayloadAuditContractAudit | None = None,
) -> set[tuple[int, int]]:
    """Return already-validated reverse-family invalids without rescanning roots."""
    if not isinstance(ledger, ResourceLedger):
        return set()
    del roots
    if contracts is None:
        contracts = ledger.audit_payload_contracts()
    _, invalid = contracts.family("reverse_add", ledger=ledger)
    return set(invalid)


__all__ = ["audit_reverse_residuals"]
