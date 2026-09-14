"""Combine independent support-owner audits without widening their policies."""

from number_compiler.resources.antihydra_payload_audit import audit_antihydra_payloads
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit, audit_physical_support_payloads,
)


def audit_support_payloads(ledger: ResourceLedger) -> PhysicalSupportPayloadAudit:
    collatz = audit_physical_support_payloads(ledger)
    if not any(row.role == "arithmetic_cylinder" for row in ledger.inventory()):
        return collatz
    antihydra = audit_antihydra_payloads(ledger)
    return PhysicalSupportPayloadAudit(
        collatz.approved | antihydra.approved, collatz.invalid | antihydra.invalid)
