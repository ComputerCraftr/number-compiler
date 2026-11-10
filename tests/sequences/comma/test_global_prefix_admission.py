"""A global provider bypasses finite prefix admission only with exact authority."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from threading import Event
from types import MappingProxyType, ModuleType, SimpleNamespace
from typing import Literal, Self

import pytest

from number_compiler.api.comma_term import CommaTermPayload
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.sequences.comma import (
    certificates,
    future_provider,
    power,
)
from number_compiler.sequences.comma.future_authority import (
    registered_global_release_artifact_sha256,
)
from number_compiler.sequences.comma.power import CommaTerm
from tests.support.comma_future_provider_fixture import (
    candidate_record,
    fixture_admission,
)


def test_fixture_and_forged_leases_cannot_bypass_global_admission(
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

    with (
        CommaTerm(1, certificate_version="stale-certificate") as term,
        CommaTerm(1) as foreign_term,
    ):
        store = future_provider.SemanticFutureProviderStore(term.ledger)
        object.__setattr__(term, "_future_provider_store", store)
        lease = store.load_record(record, charge_work=no_work_limit)
        assert lease.global_release_admitted is False
        object.__setattr__(term, "_future_provider_lease", lease)
        object.__setattr__(foreign_term, "_future_provider_store", store)
        object.__setattr__(foreign_term, "_future_provider_lease", lease)
        try:
            assert not foreign_term.has_global_future_provider
            with pytest.raises(PermissionError, match="not owned by this term"):
                foreign_term.global_future_provider_for_prefix_admission()
        finally:
            object.__setattr__(foreign_term, "_future_provider_store", None)
            object.__setattr__(foreign_term, "_future_provider_lease", None)
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
        with pytest.raises(TypeError, match="malformed future provider lease binding"):
            certificates.require_certified_index(
                1, term.ledger, term.max_work, global_provider=uninitialized
            )

        spoofed_store = object.__new__(lease_type)
        object.__setattr__(spoofed_store, "_store", SimpleNamespace(ledger=term.ledger))
        with pytest.raises(TypeError, match="malformed future provider lease binding"):
            certificates.require_certified_index(
                1, term.ledger, term.max_work, global_provider=spoofed_store
            )

        incomplete_store = object.__new__(future_provider.SemanticFutureProviderStore)
        object.__setattr__(incomplete_store, "ledger", term.ledger)
        incomplete_store_lease = object.__new__(lease_type)
        object.__setattr__(incomplete_store_lease, "_store", incomplete_store)
        object.__setattr__(incomplete_store_lease, "_digest", lease.artifact_sha256)
        forged_token = ArenaToken("comma-semantic-future-provider")
        object.__setattr__(incomplete_store_lease, "_token", forged_token)
        assert not incomplete_store_lease.global_release_admitted
        with pytest.raises(RuntimeError, match="malformed future provider store"):
            certificates.require_certified_index(
                1,
                term.ledger,
                term.max_work,
                global_provider=incomplete_store_lease,
            )

        lock_entries: list[bool] = []

        class ForgedLock:
            def __enter__(self) -> Self:
                lock_entries.append(True)
                return self

            def __exit__(self, *_args: object) -> None:
                return None

        forged_store = object.__new__(future_provider.SemanticFutureProviderStore)
        object.__setattr__(forged_store, "ledger", term.ledger)
        object.__setattr__(forged_store, "_lock", ForgedLock())
        with pytest.raises(RuntimeError, match="malformed future provider store"):
            future_provider.SemanticFutureProviderStore.resolve_checked(
                forged_store, lease.artifact_sha256, forged_token
            )
        assert lock_entries == []

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


def test_fixture_registry_does_not_resolve_global_package_resource(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()

    def no_work_limit(_amount: int) -> None:
        pass

    digest, fixture = fixture_admission(record, no_work_limit)
    admitted_instances = MappingProxyType({digest: fixture})
    monkeypatch.setattr(
        future_provider,
        "_ADMITTED_KERNEL_INSTANCES",
        admitted_instances,
    )
    fixture_registry_digest = registered_global_release_artifact_sha256(
        admitted_instances
    )
    assert fixture_registry_digest is None
    monkeypatch.setattr(
        future_provider,
        "registered_global_release_artifact_sha256",
        lambda: fixture_registry_digest,
    )

    def forbidden_resource_lookup(*_args: object, **_kwargs: object) -> object:
        pytest.fail("fixture-only authority attempted global package resource I/O")

    monkeypatch.setattr(power, "files", forbidden_resource_lookup)
    with CommaTerm(1) as term:
        assert term.global_future_provider_for_prefix_admission() is None
        assert term.retained_global_future_provider is None
        assert not term.has_global_future_provider


@pytest.mark.parametrize(
    ("artifact_contents", "expected_error"),
    ((None, FileNotFoundError), (b"not-json", ValueError)),
)
def test_registered_missing_or_corrupt_artifact_fails_closed(
    artifact_contents: bytes | None,
    expected_error: type[Exception],
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact_directory = tmp_path / "kernels"
    artifact_directory.mkdir()
    artifact = artifact_directory / future_provider.FUTURE_PROVIDER_ASSET
    if artifact_contents is not None:
        artifact.write_bytes(artifact_contents)
    monkeypatch.setattr(
        future_provider,
        "registered_global_release_artifact_sha256",
        lambda: "a" * 64,
    )

    def local_package_files(_package: str | ModuleType) -> Path:
        return tmp_path

    monkeypatch.setattr(power, "files", local_package_files)

    with CommaTerm(1, certificate_version=certificates.CERTIFICATE_ID) as term:
        with pytest.raises(expected_error):
            term.global_future_provider_for_prefix_admission()
        assert term.retained_global_future_provider is None
        assert not term.has_global_future_provider
        assert term.ledger.counters.get("comma_future_provider_closes", 0) == 1
        assert term.ledger.counters.get("comma_future_provider_publications", 0) == 0


@pytest.mark.parametrize("lifecycle", ("reset", "close"))
def test_store_lifecycle_waits_for_an_inflight_load_and_revokes_its_lease(
    lifecycle: Literal["reset", "close"],
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

    with CommaTerm(1) as term:
        store = future_provider.SemanticFutureProviderStore(term.ledger)
        entered_load = Event()
        release_load = Event()
        lifecycle_started = Event()
        lifecycle_done = Event()

        def hold_publication(amount: int) -> None:
            entered_load.set()
            if not release_load.wait(timeout=5):
                raise TimeoutError("test did not release the provider publication")
            no_work_limit(amount)

        def invalidate() -> None:
            lifecycle_started.set()
            try:
                if lifecycle == "reset":
                    store.reset()
                else:
                    store.close()
            finally:
                lifecycle_done.set()

        with ThreadPoolExecutor(max_workers=2) as workers:
            loader = workers.submit(
                store.load_record, record, charge_work=hold_publication
            )
            try:
                assert entered_load.wait(timeout=5)
                invalidator = workers.submit(invalidate)
                assert lifecycle_started.wait(timeout=5)
                lifecycle_blocked_on_load = not lifecycle_done.wait(timeout=0.05)
            finally:
                release_load.set()
            lease = loader.result(timeout=5)
            invalidator.result(timeout=5)

        assert lifecycle_blocked_on_load
        with pytest.raises(RuntimeError, match="future provider lease is stale"):
            lease.require_runtime_admission()
        store.close()


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
            object.__setattr__(term, "_future_provider_store", same_ledger_store)
            object.__setattr__(term, "_future_provider_lease", owned_lease)
            assert not term.has_global_future_provider
            with pytest.raises(PermissionError, match="not owned by this term"):
                term.global_future_provider_for_prefix_admission()

            foreign_lease = foreign_store.load_record(record, charge_work=no_work_limit)
            object.__setattr__(term, "_future_provider_store", foreign_store)
            object.__setattr__(term, "_future_provider_lease", foreign_lease)
            assert not term.has_global_future_provider
            with pytest.raises(PermissionError, match="not owned by this term"):
                term.global_future_provider_for_prefix_admission()
            with pytest.raises(ValueError, match="foreign comma global provider"):
                certificates.require_certified_index(
                    1,
                    term.ledger,
                    term.max_work,
                    global_provider=foreign_lease,
                )
        finally:
            object.__setattr__(term, "_future_provider_store", None)
            object.__setattr__(term, "_future_provider_lease", None)
            same_ledger_store.close()
            owned_store.close()
            foreign_store.close()


def test_empty_registry_refuses_all_indices_without_package_io(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> object:
        pytest.fail("empty global registry accessed package resources")

    monkeypatch.setattr(
        future_provider, "_ADMITTED_KERNEL_INSTANCES", MappingProxyType[str, object]({})
    )
    monkeypatch.setattr(power, "files", forbidden)
    with CommaTerm(1) as term:
        assert term.global_future_provider_for_prefix_admission() is None
        from number_compiler.sequences.comma.certificates import UnresolvedCommaTerm

        with pytest.raises(UnresolvedCommaTerm):
            CommaTermPayload(term).require_certified()
