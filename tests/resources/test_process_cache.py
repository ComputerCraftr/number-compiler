from __future__ import annotations

from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.resources.process_cache import (
    MISSING,
    CacheLease,
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
