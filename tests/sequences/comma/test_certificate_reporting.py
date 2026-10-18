"""Proof reporting observes admission; it must never perform admission."""

from __future__ import annotations

from types import MappingProxyType

import pytest

from number_compiler.api.comma_term import CommaTermPayload
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.process_cache import get_process_cache
from number_compiler.sequences.comma import certificates, future_provider
from number_compiler.sequences.comma.future_authority import (
    GLOBAL_RELEASE_CLAIMS,
    GLOBAL_RELEASE_CONTRACT_ID,
    GLOBAL_RELEASE_SESSION_ID,
    GLOBAL_RELEASE_THEOREM_ID,
    KERNEL_RELEASE_SCOPE,
    _KernelInstanceAdmission,
)
from number_compiler.sequences.comma.power import CommaTerm
from tests.support.comma_future_provider_fixture import candidate_record


def test_unverified_report_does_no_work_or_asset_io(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("report performed admission")

    monkeypatch.setattr(certificates, "_verify", forbidden)
    monkeypatch.setattr(certificates, "files", forbidden)
    monkeypatch.setattr(certificates, "sha256", forbidden)
    ledger = ResourceLedger()
    memo = certificates.new_certificate_memo(ledger)
    counters = dict(ledger.counters)
    for index in (1, 20_000, certificates.CERTIFIED_MAX_INDEX + 1):
        report = certificates.certificate_status(index, ledger, 1, memo=memo)
        assert report["runtime_verified"] is False
    assert ledger.counters == counters
    assert len(memo) == 0


def test_registered_global_report_is_a_metadata_only_snapshot(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("global status performed construction or artifact I/O")

    digest = "a" * 64
    monkeypatch.setattr(certificates, "_verify", forbidden)
    monkeypatch.setattr(certificates, "files", forbidden)
    monkeypatch.setattr(certificates, "sha256", forbidden)
    monkeypatch.setattr(
        certificates, "_registered_global_release_digest", lambda: digest
    )
    ledger = ResourceLedger()
    counters = dict(ledger.counters)

    report = certificates.certificate_status(
        certificates.CERTIFIED_MAX_INDEX + 100,
        ledger,
        1,
    )

    assert report["status"] == "available"
    assert report["certificate_sha256"] == digest
    assert report["certified_max_index"] is None
    assert report["runtime_verified"] is False
    assert report["isabelle_instance_checked"] is True
    assert report["coverage"] == "all_positive_indices"
    assert report["global_release_registered"] is True
    assert ledger.counters == counters


def test_global_status_rejects_an_untrusted_provider_value() -> None:
    with pytest.raises(TypeError, match="exact global provider lease"):
        certificates.certificate_status(
            certificates.CERTIFIED_MAX_INDEX + 1,
            ResourceLedger(),
            1,
            global_provider=object(),
        )


def test_admitted_global_lease_marks_runtime_status_verified(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()

    def no_work_limit(_amount: int) -> None:
        return None

    parsed = future_provider.parse_future_candidate(record, charge_work=no_work_limit)
    digest = parsed.artifact_sha256
    admission = _KernelInstanceAdmission(
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
        term._future_provider_store = store
        lease = store.load_record(record, charge_work=no_work_limit)
        term._future_provider_lease = lease
        before = dict(term.ledger.counters)
        payload = CommaTermPayload(term)
        for _ in range(3):
            assert payload.certificate_provider is lease
            report = certificates.certificate_status(
                certificates.CERTIFIED_MAX_INDEX + 1,
                term.ledger,
                1,
                global_provider=payload.certificate_provider,
            )
            assert report["status"] == "available"
            assert report["runtime_verified"] is True
            assert report["isabelle_instance_checked"] is True
            assert report["certificate_sha256"] == digest
        assert dict(term.ledger.counters) == before


@pytest.mark.parametrize("shared_cache", [False, True])
def test_reporting_retains_generation_binding_without_mutating_cache(
    shared_cache: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    cache = get_process_cache()
    ledger = ResourceLedger()
    memo = certificates.new_certificate_memo(ledger)
    # Inject the same authenticated marker that successful admission publishes.
    # This unit test checks reporting only; actual admission is covered by the
    # independent asset, forged-marker and cache-lifecycle tests.
    generation = cache.generation if shared_cache else -1
    key, tag = certificates._admission_marker(generation)
    memo[key] = tag
    counters = dict(ledger.counters)
    stats = cache.stats()

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("report performed admission")

    monkeypatch.setattr(certificates, "_verify", forbidden)
    try:
        report = certificates.certificate_status(
            1, ledger, 1, shared_cache=shared_cache, memo=memo
        )
        assert report["runtime_verified"] is True
        assert ledger.counters == counters
        assert cache.stats() == stats
        cache.reset()
        report = certificates.certificate_status(
            1, ledger, 1, shared_cache=shared_cache, memo=memo
        )
        assert report["runtime_verified"] is (not shared_cache)
        assert ledger.counters == counters
    finally:
        cache.reset()


def test_reporting_cannot_replace_value_admission(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    assert certificates.certificate_status(1, ledger, 1)["status"] == "available"

    def reject(*args: object, **kwargs: object) -> None:
        raise ValueError("no admitted evidence")

    monkeypatch.setattr(certificates, "_verify", reject)
    with pytest.raises(ValueError, match="no admitted evidence"):
        certificates.require_certified_index(1, ledger, 1)


def test_stream_admission_is_checked_on_first_pull(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[int] = []
    cache = get_process_cache()

    def admit(_self: CommaTermPayload) -> None:
        calls.append(cache.generation)

    monkeypatch.setattr(CommaTermPayload, "require_certified", admit)
    stream = CommaTermPayload(CommaTerm(1)).iter_digits()
    assert calls == []
    cache.reset()
    try:
        assert next(stream) == 0
        assert calls == [cache.generation]
    finally:
        stream.close()
        cache.reset()


def test_stream_reset_rejects_before_another_digit_is_emitted(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(CommaTermPayload, "require_certified", lambda _self: None)
    cache = get_process_cache()
    term = CommaTerm(1)
    stream = CommaTermPayload(term).iter_digits()
    try:
        assert next(stream) == 0
        emitted = term.ledger.counters["comma_stream_emitted_digits"]
        cache.reset()
        with pytest.raises(ValueError, match="stale comma stream admission"):
            next(stream)
        assert term.ledger.counters["comma_stream_emitted_digits"] == emitted
    finally:
        stream.close()
        cache.reset()
