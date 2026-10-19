"""Certified point observations use only the shared capped leaf cache."""

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.projection.microblock_cache import (
    ExactMicroblock,
    MicroblockCache,
    MicroblockKey,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


def _assert_single_scoped_point(cache: object, output_radix: int) -> None:
    assert isinstance(cache, MicroblockCache)
    blocks = cache.blocks
    assert len(blocks) == 1
    key, value = next(iter(blocks.items()))
    assert type(key) is MicroblockKey
    assert key.kind == "output"
    assert key.radix == output_radix
    assert type(key.stage) is int
    assert type(key.block) is int
    assert type(key.source_scope) is ArenaToken
    assert type(value) is ExactMicroblock
    assert value.bit_count <= 64
    assert cache.payload_bytes <= 8 * 1024


def test_collatz_point_survives_query_eviction_without_transition_replay() -> None:
    term = PoweredCollatzTerm(27, 16)
    expected = term.digit(2)
    _assert_single_scoped_point(term._microblocks, 2)
    before = dict(term.resource_ledger.counters)

    term.resource_ledger.evict_query_memos()
    assert term.digit(2) == expected

    after = term.resource_ledger.counters
    assert after.get("microblock_hits", 0) > before.get("microblock_hits", 0)
    assert after.get("nonlinear_branch_evaluations", 0) == before.get(
        "nonlinear_branch_evaluations",
        0,
    )
    assert after.get("output_morphism_visits", 0) == before.get(
        "output_morphism_visits",
        0,
    )
    assert after.get("recursive_field_image_temporal_compositions", 0) == before.get(
        "recursive_field_image_temporal_compositions",
        0,
    )
    assert after.get("temporal_parent_compositions", 0) == before.get(
        "temporal_parent_compositions",
        0,
    )
    assert after.get("new_field_image_nodes", 0) == before.get(
        "new_field_image_nodes",
        0,
    )
    assert (
        audit_registered_payloads(term.resource_ledger).forbidden_future_payloads == 0
    )


def test_collatz_capped_microblocks_retain_distinct_observed_coordinates() -> None:
    """The shared capped cache is not degraded into a one-entry register."""
    term = PoweredCollatzTerm(27, 16)
    expected = term.digit(0), term.digit(1)
    keys = tuple(key for key in term._microblocks.blocks if key.kind == "output")
    assert {key.block for key in keys} == {0, 1}
    before = dict(term.resource_ledger.counters)
    term.resource_ledger.evict_query_memos()
    assert (term.digit(0), term.digit(1)) == expected
    after = term.resource_ledger.counters
    assert after.get("output_morphism_visits", 0) == before.get(
        "output_morphism_visits",
        0,
    )


def test_fixed_collatz_cycle_uses_the_same_scoped_point_cache() -> None:
    term = PoweredCollatzTerm(1, 16)
    expected = term.digit(0)
    _assert_single_scoped_point(term._microblocks, 2)
    before = dict(term.resource_ledger.counters)
    term.resource_ledger.evict_query_memos()
    assert term.digit(0) == expected
    assert term.resource_ledger.counters.get("microblock_hits", 0) > before.get(
        "microblock_hits",
        0,
    )


def test_certified_point_rejects_a_cached_symbol_from_another_alphabet() -> None:
    term = PoweredCollatzTerm(27, 16)
    term.digit(2)
    key = next(iter(term._microblocks.blocks))
    term._microblocks.put(key, ExactMicroblock(3, 2))
    term.resource_ledger.evict_query_memos()
    with pytest.raises(ValueError, match="another alphabet"):
        term.digit(2)


def test_point_microblock_source_scopes_do_not_alias() -> None:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    effect = compiler.atom(BaseBlockEffect(10))
    program = compiler.reference(effect)
    cache = MicroblockCache(ledger, compiler.token, compiler.resolve)
    first_scope = ArenaToken("first-source")
    second_scope = ArenaToken("second-source")
    first = MicroblockKey(program, 10, 0, 0, "output", source_scope=first_scope)
    second = MicroblockKey(program, 10, 0, 0, "output", source_scope=second_scope)
    cache.put(first, ExactMicroblock(2, 4))
    cache.put(second, ExactMicroblock(7, 4))

    assert cache.get(first) == ExactMicroblock(2, 4)
    assert cache.get(second) == ExactMicroblock(7, 4)
    assert first != second


def test_generic_pair_symbol_above_radix_uses_its_admitted_alphabet() -> None:
    index = HashLifeBlockIndex(BaseBlockEffect(2), (1,), logical_length=2)
    assert index.direct_powered_point(0) == 2
    index.resource_ledger.evict_query_memos()
    assert index.direct_powered_point(0) == 2
