"""Shared fault injection for ledger-owned payload-audit publication."""

from __future__ import annotations

from collections.abc import Callable

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditStoreBinding,
)


def assert_payload_publication_released(
    ledger: ResourceLedger, root: object, family: str
) -> None:
    """Check that failed publication retains neither its contract nor storage."""
    assert (id(root), family) not in ledger._payload_audit_contracts
    assert ledger.audit_payload_contracts().invalid == frozenset()
    assert ledger.entries == ledger.nodes == 0


def fail_after_payload_audit_publication(
    monkeypatch: pytest.MonkeyPatch, failure: RuntimeError
) -> list[object]:
    """Publish through the real ledger, then fail before the caller can commit."""
    published_roots: list[object] = []
    original_register = ResourceLedger.register_payload_audit_contract

    def publish_then_fail(
        ledger: ResourceLedger,
        root: object,
        family: str,
        stores: tuple[PayloadAuditStoreBinding, ...],
        validator: Callable[[object, object], PayloadAuditContribution],
        *,
        dependencies: tuple[object, ...] = (),
    ) -> None:
        original_register(
            ledger,
            root,
            family,
            stores,
            validator,
            dependencies=dependencies,
        )
        published_roots.append(root)
        raise failure

    monkeypatch.setattr(
        ResourceLedger, "register_payload_audit_contract", publish_then_fail
    )
    return published_roots
