"""Reported audit success requires independent containers and payload coverage."""

from dataclasses import dataclass

from devtools.verification.lazy_reverse import ReverseProgram
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.fields.dyadic_tile import source_span
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics


@dataclass(frozen=True)
class _BadFuture:
    digits: tuple[int, ...]
    numerator: int


@dataclass(frozen=True)
class _Geometry:
    width: int
    shift: int


def test_payload_audit_detects_future_digits_and_unbounded_arithmetic() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("summaries", "transfer_summary")
    memo: OwnedMemo[int, object] = OwnedMemo(ledger, owner, nodes_per_entry=1)
    memo[0] = _BadFuture((1, 0, 1), 1 << 100)
    memo[1] = source_span((1, 0), blank=0, logical_length=2)
    report = collect_ledger_metrics(ledger)
    assert report.forbidden_future_payloads >= 2
    assert report.retained_unbounded_future_integers == 1
    assert report.resource_accounting_mismatch == 0
    assert report.resource_audit_unknown_payloads == 1
    assert report.resource_audit_complete == 0


def test_original_source_and_large_geometry_are_distinct_from_future_data() -> None:
    ledger = ResourceLedger()
    source_owner = ledger.register("source", "exact_source")
    source: OwnedMemo[int, object] = OwnedMemo(ledger, source_owner, nodes_per_entry=1)
    source[0] = ExactSource((1, 2), 10)
    program_owner = ledger.register("programs", "action_program")
    programs: OwnedMemo[int, object] = OwnedMemo(
        ledger, program_owner, nodes_per_entry=1
    )
    programs[0] = ReverseProgram(0, 0, 1 << 200, 0, 1 << 100, 0)
    report = collect_ledger_metrics(ledger)
    assert report.source_payload_nodes == report.action_program_nodes == 1
    assert (
        report.forbidden_future_payloads
        == report.retained_unbounded_future_integers
        == 0
    )
    assert report.resource_audit_complete == 1


def test_audit_never_calls_missing_or_unknown_coverage_complete() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("opaque", "transfer_summary")
    ledger.reserve(owner, entries=1)
    assert collect_ledger_metrics(ledger).resource_audit_complete == 0
    container = [object()]
    ledger.register_container(owner, container)
    report = collect_ledger_metrics(ledger)
    assert report.resource_unregistered_payload_resolvers == 1
    assert report.resource_audit_complete == 0
    ledger.register_container(owner, container, payloads=lambda: container)
    report = collect_ledger_metrics(ledger)
    assert report.resource_audit_unknown_payloads == 1
    assert report.resource_audit_complete == 0


def test_forged_reservation_counts_fail_independent_reconciliation() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("summary", "transfer_summary")
    actual = {0: _Geometry(10, 0)}
    ledger.register_container(
        owner, actual, node_count=lambda: len(actual), payloads=actual.values
    )
    report = collect_ledger_metrics(ledger)
    assert report.resource_observed_entries == report.resource_observed_nodes == 1
    assert report.resource_ledger_entries == report.resource_ledger_nodes == 0
    assert report.resource_accounting_mismatch == 2
    assert report.resource_audit_complete == 0


def test_field_name_alone_cannot_disguise_an_unbounded_future_coefficient() -> None:
    @dataclass(frozen=True)
    class PretendGeometry:
        offset: int
        width: int

    ledger = ResourceLedger()
    memo: OwnedMemo[int, object] = OwnedMemo(
        ledger, ledger.register("fake", "action_program")
    )
    memo[0] = PretendGeometry(1 << 100, 1 << 101)
    report = collect_ledger_metrics(ledger)
    assert report.retained_unbounded_future_integers == 2
    assert report.resource_audit_unknown_payloads == 1
    assert report.resource_audit_complete == 0


def test_radix_registry_audits_actual_projection_and_rejects_hidden_payloads() -> None:
    from number_compiler.projection.lazy_radix import collatz_radix_digit
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    term = PoweredCollatzTerm(27, 4)
    assert collatz_radix_digit(term, 3, 0) == 2
    report = collect_ledger_metrics(term._ledger)
    assert report.resource_audit_complete == 1
    assert (
        report.forbidden_future_payloads
        == report.retained_unbounded_future_integers
        == 0
    )
    projection = term._radix_projections[3]
    assert all(value is not term for value in vars(projection).values())
    # Registry auditing must traverse the actual projection, not just a handle.
    vars(projection)["digits"] = (1, 2, 0)
    vars(projection)["offset"] = 1 << 100
    bad = collect_ledger_metrics(term._ledger)
    assert bad.forbidden_future_payloads >= 1
    assert bad.retained_unbounded_future_integers == 1


def test_public_powered_metrics_do_not_run_payload_audits() -> None:
    from unittest.mock import patch

    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    term = PoweredCollatzTerm(27, 16)
    assert term.digit(0) in (0, 1)
    before = dict(term._ledger.counters)

    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("runtime metrics invoked a deep audit")

    with (
        patch(
            "number_compiler.resources.metric_collection.audit_registered_payloads",
            forbidden,
        ),
        patch(
            "number_compiler.resources.metric_collection.audit_execution_ownership",
            forbidden,
        ),
    ):
        report = term.metrics()
        assert report.temporal_diagnostics.resources.accounting_mismatch is None
        term.behavior_metrics()

    assert dict(term._ledger.counters) == before
    # The detailed collector remains the explicit path for payload auditing.
    audit = collect_ledger_metrics(term._ledger)
    assert audit.resource_audit_complete == 1
