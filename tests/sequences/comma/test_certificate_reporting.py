"""Proof reporting observes admission; it must never perform admission."""

from __future__ import annotations

import pytest

from number_compiler.api.comma_term import CommaTermPayload
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.process_cache import get_process_cache
from number_compiler.sequences.comma import certificates
from number_compiler.sequences.comma.power import CommaTerm


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
