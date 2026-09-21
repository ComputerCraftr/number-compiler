"""Adversarial checks for descriptor-only fresh-prime actions."""

from __future__ import annotations

from collections.abc import Hashable
from math import gcd
from typing import Never, cast

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageView,
)
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.successor_action import (
    PrimeSuccessorActionArena,
    PrimeSuccessorImageAdapter,
    PrimeSuccessorImagePayload,
    PrimeSuccessorSource,
)


def _direct_progression(
    limit: int, factors: tuple[int, ...], modulus: int, residue: int
) -> int:
    return sum(
        all(value % factor for factor in factors) and value % modulus == residue
        for value in range(1, limit + 1)
    )


def test_progression_recurrence_matches_direct_predicate_and_phi_owner(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    factors = (2, 3, 5, 7)
    dag = CoprimeRankDAG(factors, max_states=100_000, max_work=1_000_000)
    original = dag.count
    calls = 0

    def counted(limit: int, depth: int | None = None) -> int:
        nonlocal calls
        calls += 1
        return original(limit, depth)

    monkeypatch.setattr(dag, "count", counted)
    try:
        for limit in (0, 1, 2, 19, 100, 511):
            for residue in range(11):
                assert dag.count_progression(limit, 11, residue) == (
                    _direct_progression(limit, factors, 11, residue)
                )
        expected = sum(gcd(value, 210) == 1 for value in range(1, 501))
        assert dag.count_progression(500, 1, 0) == expected
        assert calls == 1
        assert dag.count_progression_interval(37, 212, 11, 4) == sum(
            gcd(value, 210) == 1 and value % 11 == 4 for value in range(37, 212)
        )
    finally:
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def test_partial_fresh_successor_is_the_production_rank_recurrence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.prime.select import nth_prime_at_or_after

    dag = CoprimeRankDAG((2, 3, 5, 7), max_states=100_000, max_work=1_000_000)
    try:
        for limit in (0, 1, 7, 49, 500, 4096):
            assert dag.count_via_fresh_successor(limit) == sum(
                gcd(value, 210) == 1 for value in range(1, limit + 1)
            )
    finally:
        dag.close()

    original = PrimeSuccessorImageAdapter.apply_composite
    calls = 0

    def traced(
        self: PrimeSuccessorImageAdapter,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand,
    ) -> SourceImageCandidate | None:
        nonlocal calls
        calls += 1
        return original(self, action, source, demand)

    monkeypatch.setattr(PrimeSuccessorImageAdapter, "apply_composite", traced)
    value, metrics = nth_prime_at_or_after(2, 100)
    assert value == 547
    assert calls > 0
    assert metrics.scheduler_counters
    counters = dict(metrics.scheduler_counters)
    assert counters["source_image_demanded_composite_applications"] > 0
    assert counters["prime_partial_successor_interval_projections"] > 0
    assert counters["source_image_demanded_composite_applications"] == calls
    assert counters.get("source_image_primitive_applications", 0) == 0
    assert calls < metrics.max_block_length


@pytest.mark.parametrize("max_states", range(8, 33))
def test_partial_successor_publications_respect_reduced_state_budget(
    max_states: int,
) -> None:
    from number_compiler.sequences.prime.partial_successor_image import (
        PrimePartialSuccessorQuery,
    )

    dag = CoprimeRankDAG((2, 3, 5, 7), max_states=max_states, max_work=100_000)
    query: PrimePartialSuccessorQuery | None = None
    try:
        query = PrimePartialSuccessorQuery(dag)
        try:
            query.count_primes(11, 48, 4)
        except ValueError as error:
            assert "prime state budget" in str(error)
        else:
            assert dag.ledger.entries - dag.factor_count <= max_states
            assert query.peak_scheduler_entries <= max_states
    finally:
        if query is not None:
            query.close()
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def test_exact_warm_projection_needs_no_phantom_seal_capacity() -> None:
    from number_compiler.sequences.prime.partial_successor_image import (
        PrimePartialSuccessorQuery,
    )

    dag = CoprimeRankDAG((2, 3, 5, 7), max_states=100, max_work=100_000)
    query = PrimePartialSuccessorQuery(dag)
    try:
        expected = query.count_primes(11, 48, 4)
        dag.max_states = dag.ledger.entries - dag.factor_count
        assert query.count_primes(11, 48, 4) == expected
        assert dag.ledger.entries - dag.factor_count == dag.max_states
    finally:
        query.close()
        dag.close()


def test_contained_descent_reuses_issued_stage_but_revalidates_image(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.prime.partial_successor_image import (
        PrimePartialSuccessorQuery,
    )

    dag = CoprimeRankDAG((2, 3, 5, 7), max_states=100, max_work=100_000)
    query = PrimePartialSuccessorQuery(dag)
    original_payload = PrimeSuccessorImageAdapter.validate_payload
    payload_checks = 0

    def traced_payload(adapter: PrimeSuccessorImageAdapter, payload: object) -> None:
        nonlocal payload_checks
        payload_checks += 1
        original_payload(adapter, payload)

    monkeypatch.setattr(PrimeSuccessorImageAdapter, "validate_payload", traced_payload)
    try:
        assert query.count_primes(11, 48, 4) == 11
        arena = query._arena
        publications = dag.ledger.counters.get(
            "prime_partial_successor_stage_publications", 0
        )
        before = payload_checks
        assert query.count_primes(11, 30, 4) == 6
        assert query._arena is arena
        assert (
            dag.ledger.counters.get("prime_partial_successor_stage_publications", 0)
            == publications
        )
        assert payload_checks > before
    finally:
        query.close()
        dag.close()


def test_issued_prime_prefix_is_append_only_after_stage_authentication() -> None:
    """A stage stays exact under extension; earlier factors cannot be replaced."""
    dag = CoprimeRankDAG((2, 3, 5, 7), max_states=100, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 7, parent_depth=3)
    try:
        with pytest.raises(TypeError, match="append-only"):
            dag._primes[0] = 3
        dag.append_consecutive_factor(11)
        assert arena.descriptor.parent_factors == (2, 3, 5)
        assert arena.node(arena.base).primitive
    finally:
        arena.close()
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def test_partial_stage_rejects_foreign_rank_and_factor_store_authorities() -> None:
    dag = CoprimeRankDAG((2, 3, 5, 7), max_states=100, max_work=100_000)
    foreign = CoprimeRankDAG((2, 3, 5, 7), max_states=100, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 7, parent_depth=3)
    original_store = dag._primes
    try:
        arena.rank = foreign
        with pytest.raises(ValueError, match="source authority"):
            arena.node(arena.base)
        arena.rank = dag

        object.__setattr__(dag, "_primes", foreign._primes)
        with pytest.raises(ValueError, match="source authority"):
            arena.node(arena.base)
    finally:
        object.__setattr__(dag, "_primes", original_store)
        arena.rank = dag
        arena.close()
        dag.close()
        foreign.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0
    assert foreign.ledger.entries == foreign.ledger.nodes == 0


@pytest.mark.parametrize("factors,fresh", [((2, 3), 5), ((2, 3, 5), 7)])
def test_lazy_ports_and_rank_select_match_direct_successor_wheel(
    factors: tuple[int, ...], fresh: int
) -> None:
    dag = CoprimeRankDAG(factors, max_states=100_000, max_work=2_000_000)
    arena = PrimeSuccessorActionArena(dag, fresh)
    W = arena.descriptor.parent_period
    try:
        assert arena.metrics().demanded_ports == 0
        for phase in (0, fresh - 1):
            expected = [
                value
                for value in range(1, W + 1)
                if gcd(value, W) == 1 and (value + phase) % fresh != 0
            ]
            effect = arena.port_effect(arena.base, phase)
            assert effect.surviving_values == len(expected)
            assert effect.outgoing_phase == (phase + W) % fresh
            for rank, value in enumerate(expected):
                assert arena.select(arena.base, phase, rank) == value - 1
                assert arena.rank_before(arena.base, phase, value) == rank + 1
        assert arena.metrics().demanded_ports == 2
        assert arena.metrics().parent_gap_positions_materialized == 0
    finally:
        arena.close()
        dag.close()


def test_binary_prime_cycle_closes_without_eager_ports_or_parent_gaps(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.prime import wheel_cyclotomic

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("successor action materialized a parent wheel")

    monkeypatch.setattr(wheel_cyclotomic, "extend_prime_wheel_gaps", forbidden)
    monkeypatch.setattr(wheel_cyclotomic.PrimeWheelExtensionIndex, "build", forbidden)
    factors, fresh = (2, 3, 5), 7
    dag = CoprimeRankDAG(factors, max_states=100_000, max_work=2_000_000)
    arena = PrimeSuccessorActionArena(dag, fresh)
    try:
        action = arena.power(fresh)
        # Building the action is structural.  No one of its q ports is evaluated.
        assert arena.metrics().demanded_ports == 0
        effect = arena.port_effect(action, 0)
        W = arena.descriptor.parent_period
        expected = [
            value for value in range(1, fresh * W + 1) if gcd(value, fresh * W) == 1
        ]
        assert effect.outgoing_phase == 0
        assert effect.surviving_values == len(expected)
        assert arena.metrics().demanded_ports < fresh * arena.metrics().action_nodes
        for rank in (0, 1, len(expected) // 2, len(expected) - 1):
            assert arena.select(action, 0, rank) == expected[rank] - 1
    finally:
        arena.close()
        dag.close()


def test_admitted_composed_prefix_traces_every_mark_rank_select_and_phase() -> None:
    factors, fresh, parent_depth, copies, phase = (2, 3, 5, 7), 7, 3, 7, 2
    dag = CoprimeRankDAG(factors, max_states=100_000, max_work=2_000_000)
    arena = PrimeSuccessorActionArena(dag, fresh, parent_depth=parent_depth)
    try:
        action = arena.power(copies)
        width = copies * arena.descriptor.parent_period
        expected_marks = [
            gcd(offset, arena.descriptor.parent_period) == 1
            and (offset + phase) % fresh != 0
            for offset in range(1, width + 1)
        ]
        expected_offsets = [
            offset for offset, marked in enumerate(expected_marks) if marked
        ]
        effect = arena.port_effect(action, phase)
        assert effect.surviving_values == len(expected_offsets)
        assert effect.outgoing_phase == (phase + width) % fresh
        for stop in range(width + 1):
            assert arena.rank_before(action, phase, stop) == sum(expected_marks[:stop])
        for rank, offset in enumerate(expected_offsets):
            assert arena.select(action, phase, rank) == offset
        with pytest.raises(IndexError, match=str(len(expected_offsets))):
            arena.select(action, phase, len(expected_offsets))
        assert arena.metrics().parent_gap_positions_materialized == 0
        assert arena.metrics().action_nodes < copies
    finally:
        arena.close()
        dag.close()


def test_action_identity_is_associative_and_shared_scheduler_uses_real_image() -> None:
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceBoundSchedulerCore,
        SourceImageDemand,
    )

    dag = CoprimeRankDAG((2, 3), max_states=100_000, max_work=2_000_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        a, b, c = arena.base, arena.power(2), arena.power(3)
        assert arena.compose(arena.compose(a, b), c) == arena.compose(
            a, arena.compose(b, c)
        )
        action = arena.power(8)
        source = PrimeSuccessorSource(arena.descriptor_id, 3)
        image = core.apply(adapter, source, action)
        effect = core.projection(adapter, image, SourceImageDemand("effect")).value
        assert effect == arena.port_effect(action, 3)
        selected = core.projection(
            adapter, image, SourceImageDemand("select", (5,))
        ).value
        assert selected == arena.select(action, 3, 5)
        assert core.view(image).binding.action == action
        large = arena.power(1024)
        large_image = core.apply(adapter, source, large)
        assert core.view(large_image).binding.extent == (
            1024 * arena.descriptor.parent_period
        )
        counters = dag.ledger.counters
        assert counters.get("source_image_primitive_applications", 0) <= 5
        assert counters.get("source_image_relative_transfer_hits", 0) > 0
    finally:
        core.dispose()
        arena.close()
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def test_relative_reuse_keeps_parent_wheel_phase_for_arbitrary_prefixes() -> None:
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceBoundSchedulerCore,
    )

    # W=6 and q=5 make offsets zero and five share their q-phase while occupying
    # different parent-wheel slots: value 1 survives the parent and value 6 does
    # not.  Width eleven forces a composite to start off the parent-period
    # boundary; width forty-one additionally reaches an exact translated state
    # after lcm(W, q)=30 without confusing the intervening states.
    dag = CoprimeRankDAG((2, 3), max_states=1024, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        source = PrimeSuccessorSource(arena.descriptor_id, 0)
        for width in (11, 41):
            image = core.apply(adapter, source, arena.prefix(width))
            payload = cast(PrimeSuccessorImagePayload, core.view(image).payload)
            parent = sum(gcd(value, 6) == 1 for value in range(1, width + 1))
            deleted = sum(
                gcd(value, 6) == 1 and value % 5 == 0 for value in range(1, width + 1)
            )
            assert (
                payload.parent_survivors,
                payload.deleted_survivors,
                payload.surviving_values,
                payload.outgoing_phase,
                core.view(image).binding.extent,
            ) == (parent, deleted, parent - deleted, width % 5, width)
        assert dag.ledger.counters.get("source_image_relative_transfer_hits", 0) > 0
        assert dag.ledger.entries - dag.factor_count <= 1024
    finally:
        core.dispose()
        arena.close()
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def test_cold_relative_publication_reserves_its_seal_before_capacity() -> None:
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceBoundSchedulerCore,
    )

    dag = CoprimeRankDAG((2, 3), max_states=100, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        source = PrimeSuccessorSource(arena.descriptor_id, 0)
        core.apply(adapter, source, arena.prefix(1))
        # Keep action evaluation from changing the retained baseline below.
        arena.port_effect(arena.base, 0)
        retained = dag.ledger.entries - dag.factor_count
        publications = dag.ledger.counters.get("source_image_publications", 0)
        peak_before = dag.ledger.peak_entries

        dag.max_states = retained + 3
        with pytest.raises(ValueError, match="prime state budget"):
            core.apply(adapter, source, arena.base)
        assert dag.ledger.entries - dag.factor_count == retained
        assert dag.ledger.counters.get("source_image_publications", 0) == publications
        assert dag.ledger.peak_entries <= max(
            peak_before, dag.factor_count + retained + 3
        )

        dag.max_states = retained + 4
        core.apply(adapter, source, arena.base)
        assert dag.ledger.entries - dag.factor_count == dag.max_states
        assert dag.ledger.counters["source_image_publications"] == publications + 1
        assert dag.ledger.peak_entries == max(
            peak_before, dag.factor_count + dag.max_states + 1
        )
        assert dag.ledger.counters["source_image_workspace_peak"] == 1
    finally:
        core.dispose()
        arena.close()
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def test_paired_residue_specialization_and_freshness_rejection() -> None:
    dag = CoprimeRankDAG((2, 3, 5), max_states=100_000, max_work=2_000_000)
    with pytest.raises(ValueError, match="least parent-wheel survivor"):
        PrimeSuccessorActionArena(dag, 11)
    arena = PrimeSuccessorActionArena(dag, 7, forbidden_residues=(0, 3, 3))
    try:
        assert arena.descriptor.forbidden_residues == (0, 3)
        expected = [
            value
            for value in range(1, 31)
            if gcd(value, 30) == 1 and value % 7 not in (0, 3)
        ]
        assert arena.port_effect(arena.base, 0).surviving_values == len(expected)
    finally:
        arena.close()
        dag.close()


def test_parent_authentication_scoped_ids_and_fixed_depth_survive_extension() -> None:
    invalid = CoprimeRankDAG((2, 5), max_states=100_000, max_work=2_000_000)
    try:
        with pytest.raises(ValueError, match="consecutive prime prefix"):
            PrimeSuccessorActionArena(invalid, 7)
    finally:
        invalid.close()

    first = CoprimeRankDAG((2, 3), max_states=100_000, max_work=2_000_000)
    second = CoprimeRankDAG((2, 3), max_states=100_000, max_work=2_000_000)
    left = PrimeSuccessorActionArena(first, 5)
    right = PrimeSuccessorActionArena(second, 5)
    try:
        with pytest.raises(ValueError):
            left.node(right.base)
        before = left.port_effect(left.base, 0)
        first.append_factor(5)
        # Every count remains explicitly bound to the original parent depth.
        assert left.port_effect(left.base, 0) == before
    finally:
        left.close()
        right.close()
        first.close()
        second.close()


def test_action_budget_refusal_and_close_release_every_owned_entry() -> None:
    dag = CoprimeRankDAG((2, 3), max_states=100_000, max_work=2_000_000)
    arena = PrimeSuccessorActionArena(dag, 5, max_action_entries=4)
    try:
        with pytest.raises(ValueError, match="action budget"):
            arena.power(2)
        assert arena.metrics().action_nodes == 2
        assert arena.metrics().demanded_ports == 0
    finally:
        arena.close()
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


def test_reused_partial_stage_preserves_exact_depth_type() -> None:
    from number_compiler.sequences.prime.partial_successor_image import (
        PrimePartialSuccessorQuery,
    )

    dag = CoprimeRankDAG((2,))
    query = PrimePartialSuccessorQuery(dag)
    try:
        assert query.count_primes(2, 4, 1) == 2
        for invalid in (True, 1.0, "1", None):
            with pytest.raises(ValueError, match="stage depth"):
                query.count_primes(2, 4, cast(int, invalid))
    finally:
        query.close()
        dag.close()
