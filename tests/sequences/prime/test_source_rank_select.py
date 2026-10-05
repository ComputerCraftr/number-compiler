"""Production prime rank/select must discover its own complete factor prefix."""

from math import gcd, isqrt
from typing import cast

import pytest

import number_compiler.sequences.prime.select as prime_select
from number_compiler.resources.process_cache import (
    ProcessCache,
    clear_process_cache,
    get_process_cache,
)
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.select import (
    PrimePrefixRank,
    nth_prime_at_or_after,
)

pytestmark = pytest.mark.usefixtures("isolated_process_cache")


def reference_primes(high: int) -> list[int]:
    return [n for n in range(2, high + 1) if all(n % d for d in range(2, isqrt(n) + 1))]


def factor_snapshot(owner: PrimePrefixRank) -> tuple[int, ...]:
    return owner.dag.primes


def test_counts_include_square_boundary_and_extend_past_eleven_stages() -> None:
    owner = PrimePrefixRank(max_states=131072, max_work=1000000, max_stages=4096)
    reference = reference_primes(1600)
    try:
        for high in (0, 1, 2, 3, 4, 8, 9, 48, 49, 50, 961, 1368, 1369, 1600):
            assert owner.count_leq(high) == sum(p <= high for p in reference)
        assert owner.dag.primes == tuple(p for p in reference if p <= 40)
        # A larger descriptor must not overcount when a later rank goes backwards.
        for high in range(50):
            assert owner.count_leq(high) == sum(p <= high for p in reference)
        assert owner.dag.pending_frames == 0
        assert all(row.accounting_delta == 0 for row in owner.dag.ledger.inventory())
    finally:
        owner.close()
    assert owner.dag.ledger.entries == owner.dag.ledger.nodes == 0


@pytest.mark.parametrize("start", [0, 1, 2, 3, 4, 47, 48, 49, 50, 97, 100, 1369])
def test_source_selection_matches_independent_prime_reference(start: int) -> None:
    reference = [p for p in reference_primes(1800) if p >= start]
    for index in (0, 1, 3, 10):
        actual, metrics = nth_prime_at_or_after(start, index, leaf_length=8)
        assert actual == reference[index]
        assert metrics.parent_gap_positions_materialized == 0
        if actual > 2:
            assert metrics.dag_states > 0
            assert metrics.cache_hits > 0
            assert metrics.projection_work >= metrics.dag_states
            assert (
                metrics.retained_entries == metrics.dag_states + metrics.factor_stages
            )
            assert metrics.leaf_length == 1


def test_one_dag_reuses_prefix_states_across_extension() -> None:
    dag = CoprimeRankDAG((2, 3, 5), max_states=10000, max_work=100000)
    try:
        assert dag.count(500) == sum(gcd(n, 30) == 1 for n in range(1, 501))
        states = len(dag.memo)
        hits = dag.cache_hits
        assert dag.count(500) == 134
        assert len(dag.memo) == states and dag.cache_hits == hits + 1
        dag.append_factor(7)
        assert dag.count(500) == sum(gcd(n, 210) == 1 for n in range(1, 501))
        assert dag.cache_hits > hits + 1
        assert dag.primes == (2, 3, 5, 7)
        with pytest.raises(ValueError, match="increasing"):
            dag.append_factor(3)
    finally:
        dag.close()


def test_source_image_work_cannot_escape_prime_work_budget() -> None:
    # This previously admitted 154 recurrence units plus 52 uncharged adapter
    # units. The actual source-image validation and filter must share the cap.
    with pytest.raises(ValueError, match="work budget"):
        nth_prime_at_or_after(
            2,
            10,
            max_work=154,
            max_states=10000,
            shared_cache=False,
        )
    value, metrics = nth_prime_at_or_after(
        2,
        10,
        max_work=1000,
        max_states=10000,
        shared_cache=False,
    )
    assert value == 31
    assert 0 < metrics.scheduler_work <= metrics.projection_work <= 1000


@pytest.mark.parametrize(
    "limits, message",
    [
        ({"max_states": 1, "max_work": 100000, "max_stages": 100}, "state budget"),
        ({"max_states": 10000, "max_work": 3, "max_stages": 100}, "work budget"),
        ({"max_states": 10000, "max_work": 100000, "max_stages": 1}, "stage budget"),
    ],
)
def test_budget_refusal_releases_frames_and_owned_storage(
    limits: dict[str, int], message: str
) -> None:
    owner = PrimePrefixRank(
        max_states=limits["max_states"],
        max_work=limits["max_work"],
        max_stages=limits["max_stages"],
    )
    try:
        with pytest.raises(ValueError, match=message):
            owner.count_leq(10000)
        assert owner.dag.pending_frames == 0
        assert len(owner.dag.memo) <= limits["max_states"]
        assert owner.dag.work <= limits["max_work"]
        assert len(owner.dag.primes) <= limits["max_stages"]
    finally:
        owner.close()
    assert owner.dag.ledger.entries == owner.dag.ledger.nodes == 0


def test_selector_cannot_reenter_legacy_lane_or_primality_oracles(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.prime import lane_quotient, wheel_cyclotomic
    from number_compiler.sequences.prime import set as prime_set

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError(
            "selector reentered legacy lane, bitmap or supplied prime oracle"
        )

    monkeypatch.setattr(lane_quotient, "compile_prime_block_lane_quotient", forbidden)
    monkeypatch.setattr(prime_set, "project_odd_prime_block", forbidden)
    monkeypatch.setattr(prime_set, "is_prime_u64", forbidden)
    monkeypatch.setattr(wheel_cyclotomic, "is_prime_u64", forbidden)
    monkeypatch.setattr(wheel_cyclotomic, "extend_prime_wheel_gaps", forbidden)
    monkeypatch.setattr(wheel_cyclotomic.PrimeWheelExtensionIndex, "build", forbidden)
    assert nth_prime_at_or_after(100, 100)[0] == reference_primes(1000)[125]


@pytest.mark.parametrize("bad", [True, 3.9, "3"])
def test_direct_selector_rejects_non_integer_indices(bad: object) -> None:
    with pytest.raises(TypeError):
        nth_prime_at_or_after(2, cast(int, bad))


def test_wheel_and_production_share_the_same_count_owner(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.prime.wheel_cyclotomic import _wheel_count_leq

    original = CoprimeRankDAG.count
    calls: list[CoprimeRankDAG] = []

    def counted(self: CoprimeRankDAG, limit: int, depth: int | None = None) -> int:
        calls.append(self)
        return original(self, limit, depth)

    monkeypatch.setattr(CoprimeRankDAG, "count", counted)
    _wheel_count_leq.cache_clear()
    try:
        assert _wheel_count_leq((2, 3, 5), 3, 500) == 134
        assert len(calls) == 1
        calls.clear()
        assert nth_prime_at_or_after(100, 3)[0] == 109
        assert len(calls) > 1
        assert len({id(owner) for owner in calls}) == 1
        assert calls[0].ledger.entries == 0  # disposal even if a spy retains the owner
    finally:
        _wheel_count_leq.cache_clear()


@pytest.mark.parametrize("retain_queries", [False, True])
def test_closed_workspaces_cannot_be_reused_as_an_empty_descriptor(
    retain_queries: bool,
) -> None:
    from number_compiler.resources.ownership import audit_execution_ownership

    dag = CoprimeRankDAG((2, 3), retain_queries=retain_queries)
    dag.ledger.register_execution_root(dag)
    assert dag.count(10) == 3
    assert not audit_execution_ownership(dag.ledger).violations
    if not retain_queries:
        assert len(dag.memo) == 0
    dag.close()
    assert dag.ledger.entries == 0
    with pytest.raises(RuntimeError, match="closed"):
        dag.count(10)


def test_process_reuse_keeps_source_discovery_warm_but_not_an_endpoint_cache() -> None:
    clear_process_cache()
    try:
        cold_value, cold = nth_prime_at_or_after(100_000, 10, shared_cache=True)
        warm_value, warm = nth_prime_at_or_after(100_000, 10, shared_cache=True)
        assert warm_value == cold_value
        assert cold.discovery_queries > 0
        assert warm.discovery_queries == 0
        assert warm.shared_cache_hits > 0
        assert warm.shared_cache_misses == 0
        assert warm.dag_states == 0
        assert warm.request_allocations == warm.factor_stages
        # Selection still performs each rank descent; only qualified Phi roots
        # and source-prefix evidence are retained.
        assert warm.block_compilations == cold.block_compilations
        assert warm.descent_rounds == cold.descent_rounds
        assert warm.projection_work > 0
    finally:
        clear_process_cache()


def test_warm_reuse_cannot_bypass_request_state_or_stage_limits() -> None:
    clear_process_cache()
    try:
        _, cold = nth_prime_at_or_after(10_000, 0, shared_cache=True)
        with pytest.raises(ValueError, match="state budget"):
            nth_prime_at_or_after(
                10_000,
                0,
                shared_cache=True,
                max_states=max(1, cold.dag_states - 1),
            )
        with pytest.raises(ValueError, match="stage budget"):
            nth_prime_at_or_after(
                10_000,
                0,
                shared_cache=True,
                max_stages=max(1, cold.factor_stages - 1),
            )
    finally:
        clear_process_cache()


def test_larger_cached_prefix_is_admitted_for_a_smaller_query() -> None:
    clear_process_cache()
    try:
        nth_prime_at_or_after(100_000, 0, shared_cache=True)
        value, metrics = nth_prime_at_or_after(
            100,
            3,
            shared_cache=True,
            max_states=1_000,
            max_stages=10,
        )
        assert value == 109
        assert metrics.discovery_queries == 0
        assert metrics.shared_cache_hits > 0
        assert metrics.admission_work < 20
    finally:
        clear_process_cache()


def test_generic_rank_cache_never_retains_more_than_4096_factor_stages() -> None:
    from number_compiler.resources.process_cache import ProcessCache

    cache = ProcessCache()
    with cache.acquire("generic-wheel", "v1", ("large-descriptor",)) as lease:
        # At x=1 every increasing descriptor with factors >=2 has one survivor.
        # This exercises retention admission without discovering thousands of primes.
        dag = CoprimeRankDAG(tuple(range(2, 4099)), shared_lease=lease)
        try:
            assert dag.count(1) == 1
            assert cache.stats().entries == 0
        finally:
            dag.close()


def test_foreign_public_partition_cannot_seed_the_private_prime_owner() -> None:
    clear_process_cache()
    cache = get_process_cache()
    try:
        with cache.acquire(
            "prime.coprime-rank",
            "positive-integers-least-survivor-v1",
            ("positive-integers", "consecutive-prime-prefix"),
        ) as lease:
            assert lease.put(("admitted-prefix",), (10, (2, 5), 0))
        value, metrics = nth_prime_at_or_after(100, 0, shared_cache=True)
        assert value == 101
        assert metrics.discovery_queries > 0
        assert metrics.shared_cache_misses > 0
    finally:
        clear_process_cache()


def test_shared_phi_roots_bind_the_complete_factor_descriptor() -> None:
    cache = ProcessCache(max_entries=100, max_bytes=100_000)
    with cache.acquire("test.prime", "1", ("same-source",)) as lease:
        first = CoprimeRankDAG((2, 3), shared_lease=lease)
        try:
            assert first.count(10) == 3
        finally:
            first.close()
        second = CoprimeRankDAG((2, 5), shared_lease=lease)
        try:
            assert second.count(10) == 4
            assert second.shared_hits == 0
        finally:
            second.close()


def test_failed_cover_cannot_publish_until_successful_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    clear_process_cache()
    owner = PrimePrefixRank(
        max_states=10_000,
        max_work=100_000,
        max_stages=100,
        shared_cache=True,
    )
    original_count = owner.dag.count

    def exhaust_work_after_first_append(limit: int, depth: int | None = None) -> int:
        if owner.dag.factor_count > 1:
            owner.dag.max_work = owner.dag.work
        return original_count(limit, depth)

    try:
        monkeypatch.setattr(owner.dag, "count", exhaust_work_after_first_append)
        with pytest.raises(ValueError, match="prime work budget"):
            owner.cover(25)
        assert factor_snapshot(owner) == (2, 3)
        with pytest.raises(RuntimeError, match="coverage is incomplete"):
            owner.publish()

        monkeypatch.setattr(owner.dag, "count", original_count)
        owner.dag.max_work = 100_000
        owner.cover(25)
        assert owner.covered_root == 5
        assert factor_snapshot(owner) == (2, 3, 5)
        owner.publish()
    finally:
        owner.close()

    recovered = PrimePrefixRank(
        max_states=10_000,
        max_work=100_000,
        max_stages=100,
        shared_cache=True,
    )
    try:
        recovered.cover(25)
        assert factor_snapshot(recovered) == (2, 3, 5)
        assert recovered.discovery_queries == 0
    finally:
        recovered.close()
        clear_process_cache()


def test_cached_prefix_admission_charges_each_new_entry_once() -> None:
    clear_process_cache()
    publisher = PrimePrefixRank(
        max_states=10_000,
        max_work=100_000,
        max_stages=100,
        shared_cache=True,
    )
    try:
        publisher.cover(400)
        publisher.publish()
    finally:
        publisher.close()

    owner = PrimePrefixRank(
        max_states=10_000,
        max_work=100_000,
        max_stages=100,
        shared_cache=True,
    )
    try:
        before = owner.admission_work
        owner.cover(25)
        assert factor_snapshot(owner) == (2, 3, 5)
        assert owner.admission_work - before == 5

        before = owner.admission_work
        owner.cover(49)
        assert factor_snapshot(owner) == (2, 3, 5, 7)
        assert owner.admission_work - before == 2

        before = owner.admission_work
        owner.cover(121)
        assert factor_snapshot(owner) == (2, 3, 5, 7, 11)
        assert owner.admission_work - before == 2

        admission_before = owner.admission_work
        work_before = owner.dag.work
        bit_work_before = owner.dag.arithmetic_bit_work
        owner.cover(49)
        assert owner.admission_work == admission_before
        assert owner.dag.work - work_before == 1
        assert owner.dag.arithmetic_bit_work - bit_work_before == (49).bit_length()
        assert owner.discovery_queries == 0
    finally:
        owner.close()
        clear_process_cache()


def test_cover_commits_do_not_snapshot_the_full_factor_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    clear_process_cache()
    owner = PrimePrefixRank(
        max_states=10_000,
        max_work=100_000,
        max_stages=100,
        shared_cache=True,
    )
    primes_property = CoprimeRankDAG.primes

    def reject_snapshot(_owner: CoprimeRankDAG) -> tuple[int, ...]:
        raise AssertionError("coverage commit copied the full prime prefix")

    try:
        monkeypatch.setattr(CoprimeRankDAG, "primes", property(reject_snapshot))
        owner.cover(25)
        owner.cover(49)
        assert owner.dag.factor_count == 4
        assert owner.dag.last_factor == 7

        monkeypatch.setattr(CoprimeRankDAG, "primes", primes_property)
        owner.publish()
        assert owner.shared_metrics()[-1] == 1
    finally:
        owner.close()
        clear_process_cache()


def test_publish_rejects_a_foreign_factor_store_with_matching_markers() -> None:
    owner = PrimePrefixRank(max_states=10_000, max_work=100_000, max_stages=100)
    foreign = CoprimeRankDAG((2, 3, 5), max_states=10_000, max_work=100_000)
    original_store = owner.dag._factor_store_authority
    try:
        owner.cover(25)
        assert owner.dag.factor_count == foreign.factor_count
        assert owner.dag.last_factor == foreign.last_factor
        object.__setattr__(owner.dag, "_primes", foreign._factor_store_authority)
        with pytest.raises(RuntimeError, match="coverage is incomplete"):
            owner.publish()
    finally:
        object.__setattr__(owner.dag, "_primes", original_store)
        owner.close()
        foreign.close()


@pytest.mark.parametrize("forged_root", [3, 2.0])
def test_cover_and_publish_reject_a_mutated_covered_root_without_snapshot(
    monkeypatch: pytest.MonkeyPatch,
    forged_root: object,
) -> None:
    clear_process_cache()
    owner = PrimePrefixRank(
        max_states=10_000,
        max_work=100_000,
        max_stages=100,
        shared_cache=True,
    )
    primes_property = CoprimeRankDAG.primes

    def reject_snapshot(_owner: CoprimeRankDAG) -> tuple[int, ...]:
        raise AssertionError("invalid coverage attempted a factor snapshot")

    try:
        monkeypatch.setattr(CoprimeRankDAG, "primes", property(reject_snapshot))
        object.__setattr__(owner, "covered_root", forged_root)
        with pytest.raises(RuntimeError, match="coverage is incomplete"):
            owner.cover(4)
        with pytest.raises(RuntimeError, match="coverage is incomplete"):
            owner.publish()
        assert owner.shared_metrics()[-1] == 0
    finally:
        monkeypatch.setattr(CoprimeRankDAG, "primes", primes_property)
        owner.close()
        clear_process_cache()


def test_cached_prefix_cursor_rejects_a_newly_reached_forged_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    clear_process_cache()
    source = ("test-positive-integers", "test-consecutive-prefix", b"issuer")
    monkeypatch.setattr(prime_select, "_PRIME_CACHE_SOURCE", source)
    cache = get_process_cache()
    with cache.acquire(
        "prime.coprime-rank",
        "positive-integers-least-survivor-v1",
        source,
    ) as lease:
        assert lease.put(("admitted-prefix",), (19, (2, 3, 5, 4, 19), 0))

    owner = PrimePrefixRank(
        max_states=10_000,
        max_work=100_000,
        max_stages=100,
        shared_cache=True,
    )
    try:
        owner.cover(9)
        assert owner.dag.primes == (2, 3)
        before = owner.admission_work
        with pytest.raises(RuntimeError, match="invalid shared prime prefix"):
            owner.cover(25)
        assert owner.admission_work == before + 1
        with pytest.raises(RuntimeError, match="coverage is incomplete"):
            owner.publish()
    finally:
        owner.close()
        clear_process_cache()
