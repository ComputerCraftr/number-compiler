"""Compatibility view over the reverse/add family-owned payload contracts."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit


def audit_reverse_pair_output_roots(
    ledger: ResourceLedger,
    roots: tuple[object, ...],
    containers: Mapping[int, object],
    contracts: PayloadAuditContractAudit | None = None,
) -> tuple[set[int], set[int], set[tuple[int, int]]]:
    """Return the already-audited family partition without family imports.

    ``roots`` and ``containers`` remain accepted for the legacy call shape;
    their authority is represented by the per-root contracts registered by
    each sequence owner.
    """
    del roots, containers
    audit = ledger.audit_payload_contracts() if contracts is None else contracts
    approved, invalid = audit.family("reverse_add")
    return (
        {identity for _, identity in approved},
        set(),
        set(invalid),
    )


__all__ = ["audit_reverse_pair_output_roots"]
