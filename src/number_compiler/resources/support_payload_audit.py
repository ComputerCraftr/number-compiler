"""Combine independent support-owner audits without widening their policies."""

from number_compiler.resources.dyadic_return_payload_audit import (
    audit_dyadic_return_payloads,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit,
    audit_physical_support_payloads,
)


def audit_support_payloads(
    ledger: ResourceLedger,
    contracts: PayloadAuditContractAudit | None = None,
) -> PhysicalSupportPayloadAudit:
    collatz = audit_physical_support_payloads(ledger)
    if contracts is None:
        contracts = ledger.audit_payload_contracts()
    dyadic = audit_dyadic_return_payloads(ledger, contracts)
    _antihydra_approved, antihydra_invalid = contracts.family(
        "antihydra", ledger=ledger
    )
    return PhysicalSupportPayloadAudit(
        collatz.approved | dyadic.approved,
        collatz.invalid | dyadic.invalid | antihydra_invalid,
    )
