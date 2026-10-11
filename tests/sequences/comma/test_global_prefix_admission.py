"""A global provider bypasses finite prefix admission only with exact authority."""

from __future__ import annotations

from types import MappingProxyType, SimpleNamespace

import pytest

from number_compiler.api.comma_term import CommaTermPayload
from number_compiler.sequences.comma import certificates, future_provider
from number_compiler.sequences.comma.power import CommaTerm
from tests.support.comma_future_provider_fixture import (
    candidate_record,
    fixture_admission,
)


def test_fixture_and_forged_leases_cannot_bypass_the_forest_gate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def reject_forest_fallback(*_args: object, **_kwargs: object) -> None:
        pytest.fail("invalid global authority reached the finite forest verifier")

    monkeypatch.setattr(certificates, "_verify", reject_forest_fallback)
    record = candidate_record()

    def no_work_limit(_amount: int) -> None:
        pass

    digest, fixture = fixture_admission(record, no_work_limit)
    monkeypatch.setattr(
        future_provider,
        "_ADMITTED_KERNEL_INSTANCES",
        MappingProxyType({digest: fixture}),
    )

    with (
        CommaTerm(1, certificate_version="stale-certificate") as term,
        CommaTerm(1) as foreign_term,
    ):
        store = future_provider.SemanticFutureProviderStore(term.ledger)
        term._future_provider_store = store
        lease = store.load_record(record, charge_work=no_work_limit)
        assert lease.global_release_admitted is False
        term._future_provider_lease = lease
        foreign_term._future_provider_store = store
        foreign_term._future_provider_lease = lease
        try:
            assert not foreign_term.has_global_future_provider
            with pytest.raises(PermissionError, match="not owned by this term"):
                foreign_term._global_future_provider_for_prefix_admission()
        finally:
            foreign_term._future_provider_store = None
            foreign_term._future_provider_lease = None
        with pytest.raises(ValueError, match="foreign comma global provider"):
            certificates.require_certified_index(
                1,
                foreign_term.ledger,
                foreign_term.max_work,
                global_provider=lease,
            )
        with pytest.raises(PermissionError, match="global release authority"):
            certificates.require_certified_index(
                1, term.ledger, term.max_work, global_provider=lease
            )

        lease_type = future_provider.SemanticFutureProviderLease
        uninitialized = object.__new__(lease_type)
        assert not uninitialized.runtime_admitted
        assert not uninitialized.global_release_admitted
        with pytest.raises(TypeError, match="malformed comma global provider store"):
            certificates.require_certified_index(
                1, term.ledger, term.max_work, global_provider=uninitialized
            )

        spoofed_store = object.__new__(lease_type)
        object.__setattr__(spoofed_store, "_store", SimpleNamespace(ledger=term.ledger))
        with pytest.raises(TypeError, match="malformed comma global provider store"):
            certificates.require_certified_index(
                1, term.ledger, term.max_work, global_provider=spoofed_store
            )

        incomplete_store = object.__new__(future_provider.SemanticFutureProviderStore)
        object.__setattr__(incomplete_store, "ledger", term.ledger)
        incomplete_store_lease = object.__new__(lease_type)
        object.__setattr__(incomplete_store_lease, "_store", incomplete_store)
        object.__setattr__(incomplete_store_lease, "_digest", lease.artifact_sha256)
        object.__setattr__(incomplete_store_lease, "_token", lease._token)
        assert not incomplete_store_lease.global_release_admitted
        with pytest.raises(RuntimeError, match="malformed future provider store"):
            certificates.require_certified_index(
                1,
                term.ledger,
                term.max_work,
                global_provider=incomplete_store_lease,
            )

        partial_lease = object.__new__(lease_type)
        object.__setattr__(partial_lease, "_store", store)
        object.__setattr__(partial_lease, "_digest", lease.artifact_sha256)
        with pytest.raises(TypeError, match="malformed future provider lease binding"):
            certificates.require_certified_index(
                1, term.ledger, term.max_work, global_provider=partial_lease
            )

        with pytest.raises(PermissionError, match="global release authority"):
            CommaTermPayload(term).require_certified()
        store.reset()
        with pytest.raises(RuntimeError, match="future provider lease is stale"):
            certificates.require_certified_index(
                1, term.ledger, term.max_work, global_provider=lease
            )

    with CommaTerm(1) as forged_term:
        monkeypatch.setattr(forged_term, "_future_provider_lease", object())
        with pytest.raises(PermissionError, match="not configured"):
            CommaTermPayload(forged_term).require_certified()
        with pytest.raises(TypeError, match="exact provider lease"):
            certificates.require_certified_index(
                1,
                forged_term.ledger,
                forged_term.max_work,
                global_provider=object(),
            )


def test_absent_global_lease_keeps_finite_prefix_checker(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    requests: list[tuple[object, int, bool, object]] = []

    def verify(ledger: object, max_work: int, shared_cache: bool, memo: object) -> None:
        requests.append((ledger, max_work, shared_cache, memo))

    monkeypatch.setattr(certificates, "_verify", verify)
    with CommaTerm(1, certificate_version=certificates.CERTIFICATE_ID) as term:
        CommaTermPayload(term).require_certified()
        assert requests == [
            (term.ledger, term.max_work, term.shared_cache, term.certificate_memo)
        ]


def test_term_lookup_rejects_lease_store_owned_by_another_ledger(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()

    def no_work_limit(_amount: int) -> None:
        pass

    digest, fixture = fixture_admission(record, no_work_limit)
    monkeypatch.setattr(
        future_provider,
        "_ADMITTED_KERNEL_INSTANCES",
        MappingProxyType({digest: fixture}),
    )

    with CommaTerm(1) as term, CommaTerm(1) as provider_term:
        owned_store = future_provider.SemanticFutureProviderStore(term.ledger)
        same_ledger_store = future_provider.SemanticFutureProviderStore(term.ledger)
        foreign_store = future_provider.SemanticFutureProviderStore(
            provider_term.ledger
        )
        try:
            owned_lease = owned_store.load_record(record, charge_work=no_work_limit)
            term._future_provider_store = same_ledger_store
            term._future_provider_lease = owned_lease
            assert not term.has_global_future_provider
            with pytest.raises(PermissionError, match="not owned by this term"):
                term._global_future_provider_for_prefix_admission()

            foreign_lease = foreign_store.load_record(record, charge_work=no_work_limit)
            term._future_provider_store = foreign_store
            term._future_provider_lease = foreign_lease
            assert not term.has_global_future_provider
            with pytest.raises(PermissionError, match="not owned by this term"):
                term._global_future_provider_for_prefix_admission()
            with pytest.raises(ValueError, match="foreign comma global provider"):
                certificates.require_certified_index(
                    1,
                    term.ledger,
                    term.max_work,
                    global_provider=foreign_lease,
                )
        finally:
            term._future_provider_store = None
            term._future_provider_lease = None
            same_ledger_store.close()
            owned_store.close()
            foreign_store.close()
