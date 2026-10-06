"""Exact associated-action reuse preserves source authority and small actions."""

from __future__ import annotations

from typing import cast

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.process_cache import (
    CacheRecordIssuerMismatch,
    ImmutableValue,
    ProcessCache,
)
from number_compiler.sequences.antihydra import mahler_cache
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


@pytest.fixture
def cache(monkeypatch: pytest.MonkeyPatch) -> ProcessCache:
    result = ProcessCache()
    monkeypatch.setattr(mahler_cache, "get_process_cache", lambda: result)
    return result


def _query(
    returns: int = 1024, *, shared_cache: bool = True
) -> tuple[AntihydraArithmeticTerm, dict[str, object]]:
    term = AntihydraArithmeticTerm(returns, shared_cache=shared_cache)
    # Complete arithmetic admission precedes this late Python observer demand.
    return term, associated_action(term.result())


def _forbidden(*_args: object, **_kwargs: object) -> None:
    raise AssertionError("unexpected exact Mahler construction")


def test_late_observer_warm_query_skips_exact_constructor_and_metrics_stay_read_only(
    cache: ProcessCache, monkeypatch: pytest.MonkeyPatch
) -> None:
    cold, expected = _query()
    assert cold.ledger.counters["mahler_hashlife_action_misses"] == 1
    assert cold.ledger.counters["mahler_hashlife_action_publications"] == 1
    monkeypatch.setattr(mahler_cache, "_build_action", _forbidden)
    warm, actual = _query()
    assert actual == expected
    assert warm.ledger.counters["mahler_hashlife_action_process_hits"] == 1
    assert warm.ledger.counters["mahler_hashlife_action_exact_hits"] == 1
    assert "mahler_hashlife_action_applied_hits" not in warm.ledger.counters
    before = cache.stats()
    version = warm.ledger.mutation_version
    metrics = collect_ledger_metrics(warm.ledger)
    assert metrics.resource_audit_complete
    assert metrics.resource_accounting_mismatch == 0
    assert warm.ledger.mutation_version == version
    assert cache.stats() == before
    assert before.active_leases == 0 and before.bytes > 0


@pytest.mark.parametrize("mode", ("disabled", "reset", "foreign_extent"))
def test_cache_cannot_authorize_disabled_reset_or_foreign_query(
    mode: str, cache: ProcessCache, monkeypatch: pytest.MonkeyPatch
) -> None:
    _query()
    if mode == "reset":
        cache.reset()
    monkeypatch.setattr(mahler_cache, "_build_action", _forbidden)
    with pytest.raises(AssertionError, match="unexpected exact Mahler construction"):
        _query(
            1025 if mode == "foreign_extent" else 1024, shared_cache=mode != "disabled"
        )
    assert cache.stats().active_leases == 0


@pytest.mark.parametrize("extent", (0, 1, 2, 256, 1023))
def test_small_mahler_actions_never_acquire_process_cache(
    extent: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    _, expected = _query(extent, shared_cache=False)
    # Poison the acquisition boundary itself. Extent one uses the direct
    # source-bit action shortcut and correctly publishes no cache counters.
    monkeypatch.setattr(mahler_cache, "get_process_cache", _forbidden)
    term, actual = _query(extent)
    assert actual == expected
    if extent == 1:
        assert "mahler_hashlife_action_lookups" not in term.ledger.counters


def test_changed_public_source_rejected_before_warm_cache_use(
    cache: ProcessCache,
) -> None:
    _query()
    term = AntihydraArithmeticTerm(1024)
    result = term.result()
    object.__setattr__(result, "h", result.h + 1)
    before = cache.stats()
    with pytest.raises(ValueError, match="result was changed"):
        associated_action(result)
    assert cache.stats() == before


def test_rejected_constructor_publishes_no_shared_action(
    cache: ProcessCache, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(mahler_cache, "_build_action", _forbidden)
    with pytest.raises(AssertionError, match="unexpected exact Mahler construction"):
        _query()
    stats = cache.stats()
    assert stats.entries == stats.puts == stats.active_leases == 0


def test_tiny_shared_capacity_falls_back_without_changing_exact_output(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, expected = _query(shared_cache=False)
    tiny = ProcessCache(max_entries=1)
    monkeypatch.setattr(mahler_cache, "get_process_cache", lambda: tiny)
    term, actual = _query()
    assert actual == expected
    assert term.ledger.counters["mahler_hashlife_action_bypasses"] == 1
    assert tiny.stats().entries == tiny.stats().active_leases == 0


def test_associated_action_counts_refused_issued_write(
    monkeypatch: pytest.MonkeyPatch,
    publication_blocked_cache: ProcessCache,
) -> None:
    _, expected = _query(shared_cache=False)
    constrained = publication_blocked_cache
    monkeypatch.setattr(mahler_cache, "get_process_cache", lambda: constrained)
    term, actual = _query()
    assert actual == expected
    assert term.ledger.counters["mahler_hashlife_action_bypasses"] == 1
    assert term.ledger.counters.get("mahler_hashlife_action_publications", 0) == 0
    assert constrained.stats().entries == constrained.stats().active_leases == 0


def test_cached_action_does_not_bypass_local_source_budget(cache: ProcessCache) -> None:
    _query()
    before = cache.stats()
    with pytest.raises(ValueError, match="execution budget"):
        AntihydraArithmeticTerm(1024, max_steps=1023)
    assert cache.stats() == before


@pytest.mark.parametrize("bad", (0, 1, None))
def test_invalid_cache_configuration_is_rejected(bad: object) -> None:
    with pytest.raises(TypeError, match="shared_cache"):
        AntihydraArithmeticTerm(1024, shared_cache=cast(bool, bad))


@pytest.mark.parametrize(
    "corruption",
    ("missing_cap", "zero_cap", "positive_cap", "zero_scale", "negative_scale"),
)
def test_forged_same_key_action_rejected_at_decode_boundary(
    corruption: str, cache: ProcessCache
) -> None:
    term, _ = _query()
    full_key = next(iter(cache._entries))
    partition, local_key = full_key
    wire = cache._entries[full_key][1]
    assert isinstance(wire, tuple)
    poisoned: list[ImmutableValue] = list(wire)
    if corruption.endswith("cap"):
        poisoned[4] = {"missing_cap": None, "zero_cap": (0, 1), "positive_cap": (1, 1)}[
            corruption
        ]
    else:
        poisoned[0] = 0 if corruption == "zero_scale" else -1
    with cache.acquire(*partition) as lease:
        assert lease.put_issued(
            local_key,
            tuple(poisoned),
            mahler_cache._ASSOCIATED_ACTION_PUBLISHER,
        )
    workspace = term.arithmetic_workspace
    assert workspace is not None
    # This direct demand checks rejection before the public packet's later
    # first-failure consistency check; the malformed record is never returned.
    with pytest.raises(
        (ArithmeticError, ValueError), match="two-bit failure|positive scale"
    ):
        mahler_cache.cached_associated_action(workspace)
    assert cache.stats().active_leases == 0


@pytest.mark.parametrize("corruption", ("scale", "offset", "cap"))
def test_issued_valid_shaped_action_must_match_admitted_transfer(
    corruption: str,
    cache: ProcessCache,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term, _ = _query()
    workspace = term.arithmetic_workspace
    assert workspace is not None
    full_key = next(iter(cache._entries))
    partition, local_key = full_key
    wire = cache._entries[full_key][1]
    assert type(wire) is tuple and len(wire) == 5
    poisoned = list(wire)
    if corruption == "scale":
        numerator = poisoned[0]
        assert type(numerator) is int
        poisoned[0] = numerator + 1
    elif corruption == "offset":
        numerator = poisoned[2]
        assert type(numerator) is int
        poisoned[2] = numerator + 1
    else:
        cap = poisoned[4]
        assert type(cap) is tuple and len(cap) == 2
        assert type(cap[0]) is int and type(cap[1]) is int
        poisoned[4] = (cap[0] - 1, cap[1])
    with cache.acquire(*partition) as lease:
        assert lease.put_issued(
            local_key,
            cast(ImmutableValue, tuple(poisoned)),
            mahler_cache._ASSOCIATED_ACTION_PUBLISHER,
        )
    monkeypatch.setattr(mahler_cache, "_build_action", _forbidden)
    with pytest.raises(ValueError, match="differs from the admitted transfer"):
        mahler_cache.cached_associated_action(workspace)
    counters = term.ledger.counters
    assert counters["mahler_hashlife_action_admission_rejections"] == 1
    assert counters["mahler_hashlife_failed_work"] == 1
    assert counters["mahler_hashlife_action_process_hits"] == 0
    assert cache.stats().active_leases == 0


def test_public_process_lease_cannot_forge_outer_mahler_action(
    cache: ProcessCache,
) -> None:
    term, _ = _query()
    workspace = term.arithmetic_workspace
    assert workspace is not None
    full_key = next(iter(cache._entries))
    partition, local_key = full_key
    valid_wire = cache._entries[full_key][1]
    with cache.acquire(*partition) as lease:
        assert lease.put(local_key, valid_wire)

    with pytest.raises(CacheRecordIssuerMismatch, match="publisher capability"):
        mahler_cache.cached_associated_action(workspace)
    counters = term.ledger.counters
    assert counters["mahler_hashlife_action_lookups"] == 2
    assert counters["mahler_hashlife_action_admission_rejections"] == 1
    assert counters["mahler_hashlife_failed_work"] == 1
    assert counters["mahler_hashlife_action_process_hits"] == 0
    assert cache.stats().active_leases == 0


def test_engine_cache_option_is_read_only_after_construction() -> None:
    term = AntihydraArithmeticTerm(1024, shared_cache=False)
    with pytest.raises(AttributeError):
        object.__setattr__(term.engine, "shared_cache", True)
    assert term.engine.shared_cache is False


class _AdmittedActionWorkspace:
    """Minimal post-admission view for isolating the pure action cache key."""

    def __init__(
        self,
        *,
        seed: int,
        residue: int,
        precision: int,
        lift: int,
        upper: int,
        intercept: int,
        lower: int,
    ) -> None:
        from types import SimpleNamespace

        self.seed = seed
        self.returns = 1024
        self.shared_cache = True
        self.law = ANTIHYDRA_ARITHMETIC_LAW
        self.ledger = ResourceLedger()
        self.root_source = object()
        self._source = SimpleNamespace(residue=residue, precision=precision, lift=lift)
        self._summary = SimpleNamespace(
            transfer=SimpleNamespace(upper=upper, offset=intercept, lower=lower)
        )

    def summary(self) -> object:
        return self._summary

    def source_node(self, _source: object) -> object:
        return self._source

    def mahler_root_wire(self) -> None:
        return None


def _pure_action_workspace(
    *, seed: int, residue: int, precision: int, lift: int, offset: int = 0
) -> _AdmittedActionWorkspace:
    return _AdmittedActionWorkspace(
        seed=seed,
        residue=residue,
        precision=precision,
        lift=lift,
        upper=3**1024 + offset,
        intercept=0,
        lower=2**1024,
    )


def test_pure_action_cache_reuses_equal_transfer_across_source_metadata(
    cache: ProcessCache, monkeypatch: pytest.MonkeyPatch
) -> None:
    first = _pure_action_workspace(
        seed=8,
        residue=8,
        precision=11,
        lift=17,
    )
    expected = mahler_cache.cached_associated_action(
        cast(AntihydraArithmeticImageWorkspace, first)
    )
    second = _pure_action_workspace(
        seed=40,
        residue=8,
        precision=19,
        lift=29,
    )
    monkeypatch.setattr(mahler_cache, "_build_action", _forbidden)
    actual = mahler_cache.cached_associated_action(
        cast(AntihydraArithmeticImageWorkspace, second)
    )
    assert actual == expected
    assert second.ledger.counters["mahler_hashlife_action_exact_hits"] == 1
    assert second.ledger.counters["mahler_hashlife_action_process_hits"] == 1
    assert "mahler_hashlife_action_applied_hits" not in second.ledger.counters


def test_pure_action_key_rejects_finite_alias_with_different_exact_transfer(
    cache: ProcessCache,
) -> None:
    first = _pure_action_workspace(
        seed=8,
        residue=8,
        precision=11,
        lift=17,
    )
    expected = mahler_cache.cached_associated_action(
        cast(AntihydraArithmeticImageWorkspace, first)
    )
    second = _pure_action_workspace(
        seed=40,
        residue=12,
        precision=19,
        lift=29,
        offset=1,
    )
    actual = mahler_cache.cached_associated_action(
        cast(AntihydraArithmeticImageWorkspace, second)
    )
    assert actual == mahler_cache._build_action(1024, 12, 3**1024 + 1, 0, 2**1024)
    assert actual != expected
    assert second.ledger.counters["mahler_hashlife_action_misses"] == 1
    assert second.ledger.counters["mahler_hashlife_action_exact_hits"] == 0
