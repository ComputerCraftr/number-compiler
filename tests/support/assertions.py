"""Shared assertions for observable authority and atomic-publication contracts."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import TypeVar

import pytest

from number_compiler.resources.ledger import LedgerSnapshot, ResourceLedger
from number_compiler.resources.metric_records import LedgerMetrics

T = TypeVar("T")


def assert_associative(compose: Callable[[T, T], T], a: T, b: T, c: T) -> T:
    left = compose(compose(a, b), c)
    right = compose(a, compose(b, c))
    assert left == right
    return left


def assert_rejected_atomically(
    ledger: ResourceLedger,
    operation: Callable[[], object],
    error: type[Exception] | tuple[type[Exception], ...],
    *,
    match: str | None = None,
) -> LedgerSnapshot:
    """A rejected operation must retain the complete original ledger snapshot."""
    before = ledger.snapshot()
    with pytest.raises(error, match=match):
        operation()
    assert ledger.snapshot() == before
    return before


def assert_forbidden_payloads_read_only(ledger: ResourceLedger) -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    before = ledger.snapshot()
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0
    assert ledger.snapshot() == before


def assert_mutation_rejected(
    record: object, field: str, value: object, valid: Callable[[object], bool]
) -> None:
    """Restore a forged frozen field even when an independent validator fails."""
    original = getattr(record, field)
    object.__setattr__(record, field, value)
    try:
        assert not valid(record)
    finally:
        object.__setattr__(record, field, original)


def collect_counter_quantities(
    ledger: ResourceLedger, quantities: Mapping[str, int]
) -> LedgerMetrics:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    for name, value in quantities.items():
        ledger.bump(name, value)
    report = collect_ledger_metrics(ledger)
    for name, value in quantities.items():
        assert getattr(report, name) == value
    return report


def measure_operation(
    ledger: ResourceLedger, operation: Callable[[], object]
) -> tuple[LedgerSnapshot, LedgerSnapshot]:
    before = ledger.snapshot()
    operation()
    return before, ledger.snapshot()


def assert_unallocated_hit(
    ledger: ResourceLedger, before: LedgerSnapshot, counter: str
) -> None:
    assert ledger.entries == before.entries
    assert ledger.nodes == before.nodes
    assert ledger.counters[counter] == before.counters.get(counter, 0) + 1


def assert_clean_payloads(ledger: ResourceLedger) -> None:
    from number_compiler.resources.ownership import audit_execution_ownership
    from number_compiler.resources.payload_audit import audit_registered_payloads

    assert not audit_execution_ownership(ledger).violations
    payloads = audit_registered_payloads(ledger)
    assert (
        payloads.unknown_payloads,
        payloads.forbidden_future_payloads,
        payloads.unbounded_future_integers,
    ) == (0, 0, 0)
