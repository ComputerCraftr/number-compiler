"""Shared identity checks for ledger-owned stores during payload audits."""

from __future__ import annotations

from collections.abc import Mapping, MutableSet

from number_compiler.resources.stores import LedgerDict


def audit_ledger_dict_registration(
    actual_containers: Mapping[int, object],
    owner: int,
    candidate: object,
    invalid_bindings: MutableSet[tuple[int, int]],
) -> bool:
    """Check a ledger snapshot and record invalid candidate identity on failure."""
    if actual_containers.get(owner) is candidate and type(candidate) is LedgerDict:
        return True
    invalid_bindings.add((owner, id(candidate)))
    return False


__all__ = ["audit_ledger_dict_registration"]
