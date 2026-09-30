"""Complete admitted root reuse, independent of finite quotient aliases."""

from __future__ import annotations

from fractions import Fraction
from typing import cast

import pytest

from number_compiler.api.cli_context import QueryContext
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.number_api import AntihydraTermPayload, NumberCompiler
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.process_cache import (
    CacheRecordIssuerMismatch,
    ImmutableValue,
    ProcessCache,
)
from number_compiler.sequences.antihydra import mahler_cache, mahler_source_actions
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm
from tests.support.reference_arithmetic import (
    literal_mahler_step,
    rational_action_components,
)


@pytest.fixture
def source_cache(monkeypatch: pytest.MonkeyPatch) -> ProcessCache:
    cache = ProcessCache()
    monkeypatch.setattr(mahler_source_actions, "get_process_cache", lambda: cache)
    monkeypatch.setattr(mahler_cache, "get_process_cache", lambda: cache)
    return cache


def _prepared(extent: int, *, shared_cache: bool = True) -> AntihydraArithmeticTerm:
    term = AntihydraArithmeticTerm(
        extent, shared_cache=shared_cache, max_state_bits=8192
    )
    term.prepare_mahler()
    return term


def _unexpected(*_args: object, **_kwargs: object) -> None:
    raise AssertionError("cold arithmetic construction")


@pytest.mark.parametrize("extent", (1024, 1025, 4096))
def test_complete_parent_hit_precedes_arithmetic_construction(
    extent: int, monkeypatch: pytest.MonkeyPatch, source_cache: ProcessCache
) -> None:
    cache = source_cache
    direct = AntihydraArithmeticTerm(extent, shared_cache=False, max_state_bits=8192)
    expected = associated_action(direct.result())
    cold = _prepared(extent)
    assert associated_action(cold.result()) == expected
    assert cold.ledger.counters["mahler_hashlife_source_action_publications"] == 1
    monkeypatch.setattr(
        AntihydraArithmeticImageWorkspace, "complete_composite_candidate", _unexpected
    )
    monkeypatch.setattr(
        AntihydraArithmeticImageWorkspace, "_run_candidate", _unexpected
    )
    warm = _prepared(extent)
    assert associated_action(warm.result()) == expected
    assert warm.ledger.counters["mahler_hashlife_source_action_process_hits"] == 1
    assert warm.ledger.counters["mahler_hashlife_source_action_exact_hits"] == 1
    assert warm.ledger.counters["mahler_hashlife_source_action_applied_hits"] == 1
    assert (
        warm.ledger.counters["mahler_hashlife_source_action_applied_parent_hits"] == 1
    )
    assert not warm.ledger.counters.get("antihydra_temporal_balanced_routes", 0)
    before = warm.ledger.mutation_version
    metrics = collect_ledger_metrics(warm.ledger)
    assert metrics.resource_audit_complete
    assert metrics.forbidden_future_payloads == 0
    assert metrics.resource_accounting_mismatch == 0
    assert warm.ledger.mutation_version == before
    assert cache.stats().active_leases == 0


def test_late_demand_consumes_existing_arithmetic_image(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = AntihydraArithmeticTerm(1024, shared_cache=False)
    result = term.result()
    workspace = term.arithmetic_workspace
    expected = associated_action(result)
    monkeypatch.setattr(mahler_source_actions, "get_process_cache", _unexpected)
    term.prepare_mahler()
    assert term.arithmetic_workspace is workspace
    assert associated_action(result) == expected
    assert not term._mahler_prepared


def test_retained_binding_rejects_changed_exact_cap_and_disposes() -> None:
    term = _prepared(1024, shared_cache=False)
    result = term.result()
    workspace = term.arithmetic_workspace
    assert workspace is not None and workspace.mahler_bindings is not None
    bindings = workspace.mahler_bindings
    key = workspace.root_source, workspace.root_action
    original = bindings[key]
    extent, offset, cap = original
    assert type(cap) is int
    bindings[key] = extent, offset, cap + 1
    with pytest.raises(ValueError, match="exact occurrence binding"):
        associated_action(result)
    bindings[key] = original
    owner = workspace.mahler_binding_owner
    workspace.dispose()
    assert workspace.mahler_bindings is None
    assert all(
        row.entries == row.nodes == 0
        for row in term.ledger.inventory()
        if row.owner == owner
    )


def test_integer_normal_forms_match_independent_scalar_prefixes() -> None:
    normal = mahler_source_actions.MahlerSourceBoundSafetyAction()
    source, scale, offset = 7, Fraction(1), Fraction(0)
    cap: Fraction | None = None
    for extent in range(513):
        action = normal.to_action()
        actual_scale, actual_offset, actual_cap = rational_action_components(action)
        assert actual_scale == scale
        assert actual_offset == offset
        assert actual_cap == cap
        bit = source & 1
        source, scale, offset, cap = literal_mahler_step(source, scale, offset, cap)
        normal = normal.then_with_gain(
            mahler_source_actions.MahlerSourceBoundSafetyAction(
                1, -12 * bit, 6 if bit else 18
            ),
            3,
        )


@pytest.mark.parametrize(
    "source,offset,cap", ((1, -320989428, -62709102), (41, -297684756, -39404430))
)
def test_finite_aliases_retain_distinct_exact_occurrence_coefficients(
    source: int, offset: int, cap: int
) -> None:
    normal = mahler_source_actions.MahlerSourceBoundSafetyAction()
    for _ in range(16):
        bit = source & 1
        normal = normal.then_with_gain(
            mahler_source_actions.MahlerSourceBoundSafetyAction(
                1, -12 * bit, 6 if bit else 18
            ),
            3,
        )
        source = (3 * source + bit) // 2
    assert normal.wire() == (16, offset, cap)


@pytest.mark.parametrize("corruption", ("gain", "cap_minus", "cap_plus"))
def test_poisoned_occurrence_is_rejected_before_candidate_publication(
    corruption: str,
    source_cache: ProcessCache,
) -> None:
    cache = source_cache
    cold = _prepared(1024)
    cold.result()
    with mahler_source_actions.MahlerOccurrenceConsumer(
        cold.ledger, ANTIHYDRA_ARITHMETIC_LAW, shared_cache=True
    ) as consumer:
        lease = consumer.lease
        assert lease is not None
        wire = lease.get((1024, 8))
        assert type(wire) is tuple
        altered = list(wire)
        if corruption == "gain":
            altered[2] = int(altered[2]) + 2
            altered[9] = -12 * (int(altered[2]) + int(altered[3]) - int(altered[4]))
        else:
            altered[10] = int(altered[10]) + (-1 if corruption == "cap_minus" else 1)
        assert lease.put_issued(
            (1024, 8),
            cast(tuple[ImmutableValue, ...], tuple(altered)),
            mahler_source_actions._SOURCE_ACTION_PUBLISHER,
        )
    rejected = _prepared(1024)
    with pytest.raises(ValueError, match="source/action domain|centered-11 safety cap"):
        rejected.result()
    assert not any(
        rejected.ledger.counters.get(f"mahler_hashlife_source_action_{kind}_hits", 0)
        for kind in ("exact", "transported", "local", "process")
    )
    assert not rejected.ledger.counters.get(
        "mahler_hashlife_source_action_publications", 0
    )
    assert rejected.arithmetic_workspace is None
    assert cache.stats().active_leases == 0


def test_public_process_lease_cannot_forge_mahler_source_action(
    source_cache: ProcessCache, monkeypatch: pytest.MonkeyPatch
) -> None:
    cold = _prepared(1024)
    cold.result()
    with mahler_source_actions.MahlerOccurrenceConsumer(
        cold.ledger, ANTIHYDRA_ARITHMETIC_LAW, shared_cache=True
    ) as consumer:
        lease = consumer.lease
        assert lease is not None
        wire = lease.get((1024, 8))
        assert type(wire) is tuple
        assert lease.put((1024, 8), wire)

    monkeypatch.setattr(
        AntihydraArithmeticImageWorkspace, "complete_composite_candidate", _unexpected
    )
    monkeypatch.setattr(
        AntihydraArithmeticImageWorkspace, "_run_candidate", _unexpected
    )
    rejected = _prepared(1024)
    with pytest.raises(CacheRecordIssuerMismatch, match="publisher capability"):
        rejected.result()
    counters = rejected.ledger.counters
    assert counters["mahler_hashlife_source_action_lookups"] == 1
    assert counters["mahler_hashlife_source_action_admission_rejections"] == 1
    assert counters["mahler_hashlife_failed_work"] == 1
    assert counters["mahler_hashlife_source_action_process_hits"] == 0
    assert not counters.get("mahler_hashlife_source_action_publications", 0)
    assert source_cache.stats().active_leases == 0


def test_mahler_source_action_counts_refused_gain_and_wire_writes(
    monkeypatch: pytest.MonkeyPatch,
    publication_blocked_cache: ProcessCache,
) -> None:
    cache = publication_blocked_cache
    monkeypatch.setattr(mahler_source_actions, "get_process_cache", lambda: cache)
    term = _prepared(1024)
    term.result()
    counters = term.ledger.counters
    assert counters["mahler_hashlife_source_action_bypasses"] == 2
    assert counters.get("mahler_hashlife_source_action_publications", 0) == 0
    assert cache.stats().entries == cache.stats().active_leases == 0


def test_public_cli_warm_root_skips_both_cold_arithmetic_owners(
    source_cache: ProcessCache, monkeypatch: pytest.MonkeyPatch
) -> None:
    request = parse_request(["antihydra", "--nth", "1024", "--info", "mahler"])
    assert request is not None
    cold = QueryContext(request, NumberCompiler())
    expected = cold.information()
    monkeypatch.setattr(
        AntihydraArithmeticImageWorkspace, "complete_composite_candidate", _unexpected
    )
    monkeypatch.setattr(
        AntihydraArithmeticImageWorkspace, "_run_candidate", _unexpected
    )
    warm = QueryContext(request, NumberCompiler())
    assert warm.information() == expected
    payload = warm.term.payload
    assert isinstance(payload, AntihydraTermPayload)
    assert (
        payload.term.ledger.counters[
            "mahler_hashlife_source_action_applied_parent_hits"
        ]
        == 1
    )
    assert not payload.term.ledger.counters.get("mahler_hashlife_occurrence_lookups", 0)
    assert source_cache.stats().active_leases == 0


def test_closed_occurrence_consumer_invalidates_its_local_store() -> None:
    term = _prepared(1024, shared_cache=False)
    consumer = mahler_source_actions.MahlerOccurrenceConsumer(
        term.ledger, ANTIHYDRA_ARITHMETIC_LAW, shared_cache=False
    )
    owner = consumer.records.owner
    consumer.close()
    consumer.close()
    with pytest.raises(RuntimeError, match="disposed"):
        consumer.lookup(1024, 8)
    row = next(row for row in term.ledger.inventory() if row.owner == owner)
    assert row.disposed and row.entries == row.nodes == 0
