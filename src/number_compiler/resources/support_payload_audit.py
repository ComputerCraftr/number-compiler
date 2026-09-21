"""Combine independent support-owner audits without widening their policies."""

from number_compiler.resources.antihydra_payload_audit import audit_antihydra_payloads
from number_compiler.resources.dyadic_return_payload_audit import (
    audit_dyadic_return_payloads,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit,
    audit_physical_support_payloads,
)


def audit_support_payloads(ledger: ResourceLedger) -> PhysicalSupportPayloadAudit:
    collatz = audit_physical_support_payloads(ledger)
    dyadic = audit_dyadic_return_payloads(ledger)
    if not any(row.role == "arithmetic_cylinder" for row in ledger.inventory()):
        return PhysicalSupportPayloadAudit(
            collatz.approved | dyadic.approved,
            collatz.invalid | dyadic.invalid,
        )
    antihydra = audit_antihydra_payloads(ledger, dyadic=dyadic)
    return PhysicalSupportPayloadAudit(
        collatz.approved | antihydra.approved,
        collatz.invalid | antihydra.invalid,
    )
