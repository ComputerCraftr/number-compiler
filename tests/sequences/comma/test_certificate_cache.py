"""Authenticated prefix admissions must be checked before package I/O."""

from __future__ import annotations

import builtins
from collections.abc import Mapping, Sequence

import pytest

from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.process_cache import get_process_cache
from number_compiler.sequences.comma import certificates


@pytest.mark.parametrize("shared_cache", [False, True])
def test_verified_admission_does_not_reopen_or_hash_asset(
    monkeypatch: pytest.MonkeyPatch, shared_cache: bool
) -> None:
    cache = get_process_cache()
    cache.reset()
    ledger = ResourceLedger()
    memo = certificates.new_certificate_memo(ledger)
    try:
        certificates.require_certified_index(
            1, ledger, 1_000_000, shared_cache=shared_cache, memo=memo
        )
        read_bytes = ledger.counters["comma_certificate_read_bytes"]

        def forbidden(*args: object, **kwargs: object) -> None:
            raise AssertionError("cached admission attempted package I/O or hashing")

        original_import = builtins.__import__

        def no_forest_import(
            name: str,
            globals: Mapping[str, object] | None = None,
            locals: Mapping[str, object] | None = None,
            fromlist: Sequence[str] | None = None,
            level: int = 0,
        ) -> object:
            if name == "number_compiler.sequences.comma.forest_verifier":
                raise AssertionError("cached admission imported the forest verifier")
            return original_import(name, globals, locals, fromlist, level)

        monkeypatch.setattr(certificates, "files", forbidden)
        monkeypatch.setattr(certificates, "sha256", forbidden)
        monkeypatch.setattr(builtins, "__import__", no_forest_import)
        certificates.require_certified_index(
            20, ledger, 1_000_000, shared_cache=shared_cache, memo=memo
        )
        assert ledger.counters["comma_certificate_read_bytes"] == read_bytes
        assert ledger.counters["comma_certificate_local_hits"] == 1
        if shared_cache:
            other = ResourceLedger()
            certificates.require_certified_index(100, other, 1_000_000)
            assert other.counters["comma_certificate_cache_hits"] == 1
            assert "comma_certificate_read_bytes" not in other.counters
            original_get = memo.get

            def reset_during_lookup(key: tuple[str, str]) -> str | None:
                previous = original_get(key)
                cache.reset()
                return previous

            with monkeypatch.context() as race:
                race.setattr(memo, "get", reset_during_lookup)
                with pytest.raises(RuntimeError, match="stale|invalidated"):
                    certificates.require_certified_index(
                        1, ledger, 1_000_000, memo=memo
                    )
            with pytest.raises(AssertionError, match="package I/O"):
                certificates.require_certified_index(1, ledger, 1_000_000, memo=memo)
    finally:
        cache.reset()


def test_reset_during_admission_publication_removes_failed_local_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = get_process_cache()
    cache.reset()
    try:
        certificates.require_certified_index(1, ResourceLedger(), 1_000_000)
        ledger = ResourceLedger()
        memo = certificates.new_certificate_memo(ledger)
        original_set = OwnedMemo.__setitem__

        def reset_after_set(
            store: certificates.CertificateMemo, key: tuple[str, str], value: str
        ) -> None:
            original_set(store, key, value)
            if store is memo:
                cache.reset()

        monkeypatch.setattr(OwnedMemo, "__setitem__", reset_after_set)
        with pytest.raises(RuntimeError, match="stale|invalidated"):
            certificates.require_certified_index(1, ledger, 1_000_000, memo=memo)
        assert len(memo) == 0
        assert ledger.counters.get("comma_certificate_cache_hits", 0) == 0
    finally:
        cache.reset()


def test_foreign_admission_is_rejected_before_asset_access(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("foreign authority reached package I/O")

    monkeypatch.setattr(certificates, "files", forbidden)
    memo = certificates.new_certificate_memo(ResourceLedger())
    with pytest.raises(ValueError, match="foreign comma certificate admission"):
        certificates.require_certified_index(1, ResourceLedger(), 1_000_000, memo=memo)


@pytest.mark.parametrize("marker", ["forged", "é" * 64, "x" * 100_000])
def test_forged_local_marker_is_rejected_before_asset_access(
    monkeypatch: pytest.MonkeyPatch,
    marker: str,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("forged authority reached package I/O")

    monkeypatch.setattr(certificates, "files", forbidden)
    ledger = ResourceLedger()
    memo = certificates.new_certificate_memo(ledger)
    memo[(certificates.CERTIFICATE_ID, f"{certificates.CERTIFICATE_SHA256}:-1")] = (
        marker
    )
    with pytest.raises(ValueError, match="forged comma certificate admission"):
        certificates.require_certified_index(
            1, ledger, 1_000_000, shared_cache=False, memo=memo
        )
    with pytest.raises(ValueError, match="forged comma certificate admission"):
        certificates.certificate_status(
            1, ledger, 1_000_000, shared_cache=False, memo=memo
        )


@pytest.mark.parametrize("marker", ["é" * 64, "x" * 100_000])
def test_malformed_shared_marker_is_rejected_before_asset_access(
    monkeypatch: pytest.MonkeyPatch, marker: str
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("forged shared authority reached package I/O")

    monkeypatch.setattr(certificates, "files", forbidden)
    cache = get_process_cache()
    cache.reset()
    try:
        with cache.acquire(
            "comma-prefix-certificate",
            certificates.CERTIFICATE_ID,
            (20, 10, certificates.CERTIFICATE_SHA256),
        ) as lease:
            assert lease.put(
                (
                    certificates.CERTIFIED_MAX_INDEX,
                    certificates.FIRST_FORK_INDEX,
                    certificates.FIRST_FORK_VALUE,
                ),
                (certificates.CERTIFICATE_SHA256, marker),
            )
        with pytest.raises(ValueError, match="foreign comma certificate cache"):
            certificates.require_certified_index(1, ResourceLedger(), 1_000_000)
    finally:
        cache.reset()
