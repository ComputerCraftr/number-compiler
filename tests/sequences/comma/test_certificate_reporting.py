"""Global release status is metadata-only and never performs admission."""

from __future__ import annotations

from types import MappingProxyType

import pytest

from number_compiler.api.comma_term import CommaTermPayload
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import comma as comma_metrics
from number_compiler.sequences.comma import certificates, future_provider
from number_compiler.sequences.comma.future_authority import (
    GLOBAL_RELEASE_CLAIMS,
    GLOBAL_RELEASE_CONTRACT_ID,
    GLOBAL_RELEASE_SESSION_ID,
    GLOBAL_RELEASE_THEOREM_ID,
    KERNEL_RELEASE_SCOPE,
    KernelInstanceAdmission,
)
from number_compiler.sequences.comma.power import CommaTerm
from tests.support.comma_future_provider_fixture import candidate_record


def test_empty_registry_status_is_metadata_only(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(certificates, "_registered_global_release_digest", lambda: None)
    ledger = ResourceLedger()
    before = dict(ledger.counters)
    for index in (1, 20000, 10**40):
        status = certificates.certificate_status(index, ledger, 1)
        assert status["status"] == "unknown"
        assert status["certified_max_index"] is None
        assert status["coverage"] == "none"
        assert status["runtime_verified"] is False
    assert dict(ledger.counters) == before
    with pytest.raises(certificates.UnresolvedCommaTerm):
        certificates.require_certified_index(1, ledger, 1)


def test_registered_global_report_is_metadata_only(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    digest = "a" * 64
    monkeypatch.setattr(
        certificates, "_registered_global_release_digest", lambda: digest
    )
    ledger = ResourceLedger()
    before = dict(ledger.counters)
    status = certificates.certificate_status(10**40, ledger, 1)
    assert status["status"] == "available"
    assert status["certificate_sha256"] == digest
    assert status["certified_max_index"] is None
    assert status["coverage"] == "all_positive_indices"
    assert status["runtime_verified"] is False
    assert dict(ledger.counters) == before


def test_exact_global_lease_marks_runtime_status_verified(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def no_work_limit(_amount: int) -> None:
        return None

    record = candidate_record()
    parsed = future_provider.parse_future_candidate(record, charge_work=no_work_limit)
    digest = parsed.artifact_sha256
    admission = KernelInstanceAdmission(
        artifact_sha256=digest,
        instance_id=GLOBAL_RELEASE_SESSION_ID,
        theorem_id=GLOBAL_RELEASE_THEOREM_ID,
        contract_id=GLOBAL_RELEASE_CONTRACT_ID,
        claims=GLOBAL_RELEASE_CLAIMS,
        scope=KERNEL_RELEASE_SCOPE,
    )
    monkeypatch.setattr(
        future_provider,
        "_ADMITTED_KERNEL_INSTANCES",
        MappingProxyType({digest: admission}),
    )
    monkeypatch.setattr(
        future_provider, "registered_global_release_artifact_sha256", lambda: digest
    )
    with CommaTerm(1) as term:
        store = future_provider.SemanticFutureProviderStore(term.ledger)
        object.__setattr__(term, "_future_provider_store", store)
        lease = store.load_record(record, charge_work=no_work_limit)
        object.__setattr__(term, "_future_provider_lease", lease)
        before = dict(term.ledger.counters)
        payload = CommaTermPayload(term)
        for _ in range(3):
            assert payload.certificate_provider is lease
            status = certificates.certificate_status(
                10**40, term.ledger, 1, global_provider=payload.certificate_provider
            )
            assert status["status"] == "available"
            assert status["runtime_verified"] is True
            assert status["certificate_sha256"] == digest
        assert dict(term.ledger.counters) == before

        work_before = term.ledger.counters.get(
            comma_metrics.COMMA_WORK, 0
        ) + term.ledger.counters.get(comma_metrics.COMMA_CERTIFICATE_WORK, 0)
        certificates.require_certified_index(
            10**40, term.ledger, work_before + 1, global_provider=lease
        )
        after_admission = dict(term.ledger.counters)
        assert (
            after_admission[comma_metrics.COMMA_CERTIFICATE_WORK]
            == before.get(comma_metrics.COMMA_CERTIFICATE_WORK, 0) + 1
        )
        assert (
            after_admission[comma_metrics.COMMA_GLOBAL_RELEASE_PREFIX_ADMISSIONS]
            == before.get(comma_metrics.COMMA_GLOBAL_RELEASE_PREFIX_ADMISSIONS, 0) + 1
        )
        with pytest.raises(BlockContextBudgetExceeded):
            certificates.require_certified_index(
                10**40,
                term.ledger,
                work_before + 1,
                global_provider=lease,
            )
        assert (
            term.ledger.counters.get(
                comma_metrics.COMMA_GLOBAL_RELEASE_PREFIX_ADMISSIONS, 0
            )
            == after_admission[comma_metrics.COMMA_GLOBAL_RELEASE_PREFIX_ADMISSIONS]
        )
