from __future__ import annotations

import gc
from concurrent.futures import ThreadPoolExecutor
from threading import Barrier
from typing import cast
from weakref import ref

import pytest

from number_compiler.api.query_types import FermatTermQuery
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.resources.process_cache import (
    MISSING,
    CacheLease,
    CacheRecordIssuerMismatch,
    ImmutableValue,
    ProcessCache,
)


def test_source_qualified_lease_does_not_cross_partitions() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    with cache.acquire("prime", "1", ("source-a",)) as first:
        assert first.put(("phi", 2, 100), 33)
        assert first.get(("phi", 2, 100)) == 33
    with cache.acquire("prime", "1", ("source-b",)) as foreign:
        assert foreign.get(("phi", 2, 100)) is MISSING
    with cache.acquire("prime", "2", ("source-a",)) as newer_version:
        assert newer_version.get(("phi", 2, 100)) is MISSING


def test_record_issuer_is_identity_checked_and_included_in_retained_bytes() -> None:
    issuer = object()
    foreign = object()
    ordinary_cache = ProcessCache(max_entries=8, max_bytes=100_000)
    issued_cache = ProcessCache(max_entries=8, max_bytes=100_000)
    with ordinary_cache.acquire("family", "1", ("source",)) as ordinary:
        assert ordinary.put(("effect",), (1, 2, 3))
        with pytest.raises(CacheRecordIssuerMismatch):
            ordinary.get_issued(("effect",), issuer)
    with issued_cache.acquire("family", "1", ("source",)) as issued:
        assert issued.put_issued(("effect",), (1, 2, 3), issuer)
        assert issued.get_issued(("effect",), issuer) == (1, 2, 3)
        with pytest.raises(CacheRecordIssuerMismatch):
            issued.get_issued(("effect",), foreign)
        with pytest.raises(TypeError, match="exact object capability"):
            issued.get_issued(("effect",), "family")
    assert issued_cache.stats().bytes > 0
    assert ordinary_cache.stats().bytes > 0


def test_unissued_reader_cannot_consume_another_producers_record() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    issuer = object()
    partition = ("shared-namespace", "v1", ("source",))
    with cache.acquire(*partition) as producer:
        assert producer.put_issued(("payload",), ("producer-a",), issuer)

    # Namespace, version, and source keys are caller-defined. If two families
    # accidentally collide there, a non-issued reader must still fail closed.
    with cache.acquire(*partition) as foreign_reader:
        with pytest.raises(CacheRecordIssuerMismatch):
            foreign_reader.get(("payload",))
        with pytest.raises(CacheRecordIssuerMismatch):
            foreign_reader.get_issued(("payload",), object())
        assert foreign_reader.get_issued(("payload",), issuer) == ("producer-a",)


def test_issued_record_updates_are_atomic_and_preserve_all_concurrent_writes() -> None:
    cache = ProcessCache(max_entries=128, max_bytes=100_000)
    issuer = object()
    partition = ("family", "atomic-v1", ("source",))
    workers = 24
    start = Barrier(workers)

    def publish(value: int) -> bool:
        with cache.acquire(*partition) as lease:
            start.wait()

            def append(existing: object) -> tuple[ImmutableValue, int]:
                if existing is MISSING:
                    records: tuple[ImmutableValue, ...] = ()
                else:
                    assert type(existing) is tuple
                    records = cast(tuple[ImmutableValue, ...], existing)
                return (*records, (value,)), value

            return lease.update_issued(("records",), issuer, append)[0] is True

    with ThreadPoolExecutor(max_workers=workers) as pool:
        assert all(pool.map(publish, range(workers)))

    with cache.acquire(*partition) as reader:
        retained = reader.get_issued(("records",), issuer)
        assert type(retained) is tuple
        rows = cast(tuple[tuple[int, ...], ...], retained)
        assert set(rows) == {(value,) for value in range(workers)}
        updater_called = False

        def forbidden_update(value: object) -> tuple[object, None]:
            nonlocal updater_called
            updater_called = True
            return value, None

        foreign = cache.acquire(*partition)
        with foreign, pytest.raises(CacheRecordIssuerMismatch):
            foreign.update_issued(("records",), object(), forbidden_update)
        assert not updater_called
    assert cache.stats().entries == 1
    assert cache.stats().bytes > 0


def test_issued_update_respects_capacity_and_stale_generation() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=8_000)
    issuer = object()
    lease = cache.acquire("family", "atomic-v1", ("source",))
    assert lease.put_issued(("records",), ((1,),), issuer)
    before = cache.stats()
    assert lease.update_issued(
        ("records",), issuer, lambda _value: ((b"x" * 16_000,), None)
    ) == (False, None)
    assert lease.get_issued(("records",), issuer) == ((1,),)
    assert cache.stats().bytes == before.bytes

    def fail_update(_value: object) -> tuple[object, None]:
        raise RuntimeError("injected update failure")

    with pytest.raises(RuntimeError, match="injected update failure"):
        lease.update_issued(("records",), issuer, fail_update)
    assert lease.get_issued(("records",), issuer) == ((1,),)

    cache.reset()
    updater_called = False

    def stale_update(value: object) -> tuple[object, None]:
        nonlocal updater_called
        updater_called = True
        return value, None

    with pytest.raises(RuntimeError, match="stale"):
        lease.update_issued(("records",), issuer, stale_update)
    assert not updater_called
    lease.close()


def test_issued_update_revalidates_authority_when_reset_returns_missing() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    issuer = object()
    lease = cache.acquire("family", "atomic-v1", ("source",))
    assert lease.put_issued(("records",), ((1,),), issuer)

    def reset_without_replacement(_value: object) -> tuple[object, str]:
        cache.reset()
        return MISSING, "reset"

    with pytest.raises(RuntimeError, match="stale after reset"):
        lease.update_issued(("records",), issuer, reset_without_replacement)
    assert cache.stats().entries == cache.stats().active_leases == 0
    lease.close()


def test_issued_update_revalidates_authority_when_callback_closes_lease() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    issuer = object()
    lease = cache.acquire("family", "atomic-v1", ("source",))
    assert lease.put_issued(("records",), ((1,),), issuer)

    def close_without_replacement(_value: object) -> tuple[object, str]:
        lease.close()
        return MISSING, "closed"

    with pytest.raises(RuntimeError, match="foreign authority"):
        lease.update_issued(("records",), issuer, close_without_replacement)
    assert cache.stats().entries == 1
    assert cache.stats().active_leases == 0


def test_nested_same_key_update_wins_over_outer_update() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    issuer = object()
    with cache.acquire("family", "atomic-v1", ("source",)) as lease:
        nested = False

        def update(value: object) -> tuple[ImmutableValue, str]:
            nonlocal nested
            if not nested:
                nested = True
                assert lease.update_issued(("records",), issuer, update) == (
                    True,
                    "nested",
                )
                return (("outer",),), "outer"
            assert value is MISSING
            return (("nested",),), "nested"

        assert lease.update_issued(("records",), issuer, update) == (
            False,
            "outer",
        )
        assert lease.get_issued(("records",), issuer) == (("nested",),)


def test_issued_record_authority_cannot_be_replaced_by_another_writer() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    issuer = object()
    foreign_issuer = object()
    with cache.acquire("family", "1", ("source",)) as lease:
        assert lease.put_issued(("record",), (("original",),), issuer)

        with pytest.raises(CacheRecordIssuerMismatch):
            lease.put(("record",), (("plain replacement",),))
        with pytest.raises(CacheRecordIssuerMismatch):
            lease.put_issued(("record",), (("foreign replacement",),), foreign_issuer)

        # The owning publisher may still intentionally replace its own record.
        assert lease.put_issued(("record",), (("owner replacement",),), issuer)
        assert lease.get_issued(("record",), issuer) == (("owner replacement",),)


def test_issued_record_cannot_be_claimed_over_an_unissued_record() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    with cache.acquire("family", "1", ("source",)) as lease:
        assert lease.put(("record",), (("plain",),))
        with pytest.raises(CacheRecordIssuerMismatch):
            lease.put_issued(("record",), (("claimed",),), object())
        assert lease.get(("record",)) == (("plain",),)


def test_issued_record_capacity_refusal_is_bounded_and_nonmutating() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=2_000)
    with cache.acquire("family", "1", ("source",)) as lease:
        before = cache.stats()
        assert not lease.put_issued(("large",), b"x" * 4_000, object())
        after = cache.stats()
        assert after.entries == before.entries == 0
        assert after.bytes == before.bytes
        assert lease.get_issued(("large",), object()) is MISSING


def test_boolean_integer_aliases_cannot_cross_cache_authority_keys() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    # Python considers these tuple keys equal. Reject the ambiguous key at
    # admission, including nested components, while allowing Boolean payloads.
    with pytest.raises(TypeError, match="Boolean key components"):
        cache.acquire("prime", "1", (True,))
    with cache.acquire("prime", "1", (1,)) as lease:
        with pytest.raises(TypeError, match="Boolean key components"):
            lease.put(("phi", (False,)), 7)
        assert lease.put(("phi", 0), True)
        assert lease.get(("phi", 0)) is True
    assert cache.stats().entries == 1


def test_reset_invalidates_existing_authority_and_releases_accounting() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    lease = cache.acquire("prime", "1", ("positive-integers",))
    assert lease.put(("prefix",), (31, (2, 3, 5, 7)))
    before = cache.stats()
    assert before.entries == 1 and before.active_leases == 1
    assert before.bytes > 0 and cache.ledger.nodes > 0

    cache.reset()

    after = cache.stats()
    assert after.entries == after.lease_partitions == after.bytes == 0
    assert after.active_leases == 0
    assert after.generation == before.generation + 1
    assert cache.ledger.entries == cache.ledger.nodes == 0
    with pytest.raises(RuntimeError, match="stale"):
        lease.get(("prefix",))
    lease.close()


def test_lru_eviction_is_deterministic_and_never_evicts_a_leased_partition() -> None:
    cache = ProcessCache(max_entries=6, max_bytes=100_000)
    with cache.acquire("counts", "1", ("old",)) as old:
        assert old.put(("a",), 1)
        assert old.put(("b",), 2)

    with cache.acquire("counts", "1", ("active",)) as active:
        assert active.put(("held",), 3)
        # Five retained entries: three payloads, one source partition, and one
        # exact issued-lease authority.  The next payload fills the cache.
        assert active.put(("new",), 4)
        assert active.get(("held",)) == 3
        assert active.get(("new",)) == 4
        # No room remains.  The oldest unleased payload can be evicted, but
        # payloads in the active source partition cannot.
        assert active.put(("newer",), 5)
        assert active.get(("held",)) == 3
        assert active.get(("new",)) == 4
        assert active.get(("newer",)) == 5
    assert cache.stats().evictions == 1
    with cache.acquire("counts", "1", ("old",)) as old:
        assert old.get(("a",)) is MISSING
        assert old.get(("b",)) == 2


def test_all_pinned_capacity_refuses_publication_without_mutation() -> None:
    cache = ProcessCache(max_entries=4, max_bytes=100_000)
    with cache.acquire("counts", "1", ("active",)) as lease:
        assert lease.put(("first",), 1)
        assert lease.put(("second",), 2)
        before = cache.stats()
        assert not lease.put(("third",), 3)
        after = cache.stats()
        assert after.entries == before.entries
        assert after.bytes == before.bytes
        assert after.bypasses == before.bypasses + 1
        assert lease.get(("first",)) == 1
        assert lease.get(("second",)) == 2


def test_byte_cap_and_external_accounting_cannot_be_understated() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=2_000)
    with cache.acquire("bytes", "1", ("source",)) as lease:
        with pytest.raises(ValueError, match="conservative estimate"):
            lease.put(("small",), 1, accounted_bytes=1)
        before = cache.stats()
        assert not lease.put(("large",), b"x" * 10_000)
        after = cache.stats()
        assert after.entries == before.entries == 0
        assert after.bytes == before.bytes


def test_immutable_wire_domain_rejects_mutable_or_behavioral_payloads() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    with pytest.raises(ValueError, match="identify a source"):
        cache.acquire("bad", "1", ())
    with pytest.raises(TypeError, match="source qualification"):
        cache.acquire("bad", "1", cast(tuple[ImmutableValue, ...], ([1],)))
    with cache.acquire("good", "1", ("source",)) as lease:
        with pytest.raises(TypeError, match="cache key"):
            lease.get(cast(tuple[ImmutableValue, ...], ({"mutable": 1},)))
        with pytest.raises(TypeError, match="cache payload"):
            lease.put(("value",), cast(ImmutableValue, [1, 2]))


def test_disabled_cache_bypasses_payload_storage_but_accounts_lease_records() -> None:
    cache = ProcessCache(
        max_entries=8,
        max_bytes=100_000,
        enabled=False,
    )
    with cache.acquire("prime", "1", ("source",)) as lease:
        assert lease.get(("missing",)) is MISSING
        assert not lease.put(("value",), 17)
        active = cache.stats()
        assert active.active_leases == active.lease_partitions == 1
        assert active.bytes > 0
    stats = cache.stats()
    assert stats.entries == stats.lease_partitions == stats.bytes == 0
    assert stats.active_leases == 0 and stats.bypasses == 2


def test_disabled_cache_rejects_forged_reconstructed_and_mutated_leases() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000, enabled=False)
    real = cache.acquire("prime", "1", ("source",))
    token = real._token
    forged = CacheLease(
        cache,
        ("prime", "1", ("foreign",)),
        cache.generation,
        _token=token,
    )
    with pytest.raises(RuntimeError, match="foreign authority"):
        forged.get(("value",))
    reconstructed = CacheLease(
        cache,
        real.source_qualification,
        cache.generation,
        _token=token,
    )
    with pytest.raises(RuntimeError, match="foreign authority"):
        reconstructed.put(("value",), 1)

    original_partition = real.source_qualification
    real._partition = "prime", "1", ("mutated",)
    with pytest.raises(RuntimeError, match="foreign authority"):
        real.get(("value",))
    real._partition = original_partition
    real.close()
    assert cache.stats().active_leases == 0


def test_disabled_cache_reset_invalidates_lease_without_foreign_release() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000, enabled=False)
    lease = cache.acquire("prime", "1", ("source",))
    before = cache.stats()
    assert before.active_leases == 1 and before.bytes > 0
    cache.reset()
    with pytest.raises(RuntimeError, match="stale"):
        lease.get(("value",))
    lease.close()
    after = cache.stats()
    assert after.active_leases == after.lease_partitions == after.bytes == 0


def test_oversized_source_lease_is_rejected_without_eviction() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=4_000)
    with cache.acquire("small", "1", ("source",)) as lease:
        assert lease.put(("value",), 1)
    before = cache.stats()
    with pytest.raises(BlockContextBudgetExceeded):
        cache.acquire("large", "1", ("x" * 10_000,))
    after = cache.stats()
    assert after.entries == before.entries
    assert after.bytes == before.bytes
    assert after.evictions == before.evictions


def test_lease_close_is_idempotent_and_closed_lease_cannot_be_reused() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    lease = cache.acquire("prime", "1", ("source",))
    lease.close()
    lease.close()
    assert cache.stats().active_leases == 0
    with pytest.raises(RuntimeError, match="closed"):
        lease.get(("value",))


def test_failed_close_keeps_lease_recoverable_and_releases_its_pin() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    lease = cache.acquire("prime", "1", ("source",))
    original = lease.source_qualification
    lease._partition = ("prime", "1", ("other",))
    with pytest.raises(RuntimeError, match="foreign authority"):
        lease.close()
    assert cache.stats().active_leases == 1
    lease._partition = original
    lease.close()
    assert cache.stats().active_leases == 0
    assert cache.stats().lease_partitions == 0
    assert cache.ledger.entries == cache.ledger.nodes == 0


def test_issued_lease_rejects_numeric_alias_mutations_before_cache_access() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    cache.reset()  # Both the next token and generation equal integer one.
    lease = cache.acquire("prime", "1", (1,))
    assert lease.put((0,), 19)
    issued = lease.source_qualification
    for field, alias in (
        ("_partition", ("prime", "1", (True,))),
        ("_token", True),
        ("_generation", True),
        ("_generation", 1.0),
    ):
        original = getattr(lease, field)
        setattr(lease, field, alias)
        try:
            with pytest.raises(RuntimeError, match="foreign authority"):
                lease.get((0,))
            with pytest.raises(RuntimeError, match="foreign authority"):
                lease.close()
            assert cache.stats().active_leases == 1
        finally:
            setattr(lease, field, original)
    assert lease.source_qualification is issued
    assert lease.get((0,)) == 19
    lease.close()
    assert cache.stats().active_leases == 0


def test_active_lease_cannot_close_as_a_forged_stale_generation_or_token() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    cache.reset()
    lease = cache.acquire("prime", "1", ("source",))
    assert lease.put(("state",), 7)
    for field, forged in (
        ("_generation", cache.generation + 1),
        ("_generation", cache.generation - 1),
        ("_token", lease._token + 1),
    ):
        original = getattr(lease, field)
        setattr(lease, field, forged)
        try:
            with pytest.raises(RuntimeError, match="foreign authority"):
                lease.close()
            assert cache.stats().active_leases == 1
            assert cache.stats().lease_partitions == 1
        finally:
            setattr(lease, field, original)
    assert lease.get(("state",)) == 7
    lease.close()
    assert cache.stats().active_leases == 0
    assert cache.stats().lease_partitions == 0


def test_dropped_unclosed_lease_keeps_its_issued_identity_until_reset() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    forgotten = cache.acquire("prime", "1", ("first",))
    forgotten_ref = ref(forgotten)
    issued_id = id(forgotten)
    del forgotten
    gc.collect()
    assert forgotten_ref() is not None

    next_lease = cache.acquire("prime", "1", ("second",))
    assert id(next_lease) != issued_id
    assert cache.stats().active_leases == 2
    assert cache.stats().lease_partitions == 2
    cache.reset()
    next_lease.close()  # A genuinely stale lease is harmless after reset.
    del next_lease
    gc.collect()
    assert forgotten_ref() is None
    assert cache.stats().active_leases == 0
    assert cache.ledger.entries == cache.ledger.nodes == 0


def test_ledger_reserve_refusal_does_not_publish_a_phantom_lease() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    cache.ledger.tighten_limits(0, None)
    with pytest.raises(BlockContextBudgetExceeded, match="node budget"):
        cache.acquire("prime", "1", ("source",))
    stats = cache.stats()
    assert stats.active_leases == stats.lease_partitions == stats.bytes == 0
    assert stats.entries == 0
    assert cache.ledger.entries == cache.ledger.nodes == 0


def test_forged_and_foreign_lease_authority_is_rejected() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    real = cache.acquire("prime", "1", ("source",))
    forged = CacheLease(
        cache,
        ("prime", "1", ("foreign-source",)),
        cache.generation,
        _token=real._token,
    )
    with pytest.raises(RuntimeError, match="foreign authority"):
        forged.get(("value",))
    reconstructed = CacheLease(
        cache,
        real.source_qualification,
        cache.generation,
        _token=real._token,
    )
    with pytest.raises(RuntimeError, match="foreign authority"):
        reconstructed.get(("value",))
    real.close()


def test_cache_has_no_unregistered_persistent_stores() -> None:
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    with cache.acquire("prime", "1", ("source",)) as lease:
        assert lease.put(("phi", 2, 10), 5)
        report = audit_execution_ownership(cache.ledger)
        assert not report.violations


def test_cli_cache_snapshot_neither_constructs_nor_changes_cache(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api.cli_render import _metrics_json
    from number_compiler.api.number_api import NumberCompiler
    from number_compiler.resources import process_cache

    term = NumberCompiler(shared_cache=False).project(FermatTermQuery(2))
    monkeypatch.setattr(process_cache, "_PROCESS_CACHE", None)

    def forbidden() -> ProcessCache:
        raise AssertionError("metrics created a shared cache")

    monkeypatch.setattr(process_cache, "get_process_cache", forbidden)
    assert _metrics_json(term)["process_cache"] is None
    cache = ProcessCache(max_entries=8, max_bytes=100_000)
    with cache.acquire("snapshot-test", "1", ("source",)) as lease:
        lease.put(("germ",), (1, 3))
    monkeypatch.setattr(process_cache, "_PROCESS_CACHE", cache)
    before = cache.stats()
    payload = _metrics_json(term)
    assert payload["process_cache_scope"] == "process_aggregate_not_query_work"
    assert isinstance(payload["process_cache"], dict)
    assert payload["process_cache"]["entries"] == 1
    assert cache.stats() == before
