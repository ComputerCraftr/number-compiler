"""Complete mixed actions are reused before cold selector discovery."""

from __future__ import annotations

from typing import cast

import pytest

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.process_cache import CacheLease, ProcessCache
from number_compiler.sequences.collatz import (
    mixed_action_cache,
    mixed_clock_macros,
    source_cylinder_cache,
    temporal_mixed_execution,
    temporal_run_executor,
    temporal_unified_skew_execution,
)
from number_compiler.sequences.collatz.border_identity import MixedParityMotif
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.mixed_action_cache import (
    MAX_RECORDS_PER_PREFIX,
    lookup_mixed_action,
    merge_mixed_action_records,
    remember_mixed_action,
)
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)
from tests.support.reference_arithmetic import collatz_literal

_D68_SOURCE = (1 << 160) + 48_233_076_155_686_138_603
_D68_PHYSICAL_TICKS = 108
_QUERY_PHYSICAL_TICKS = 128


def _wire_cache(monkeypatch: pytest.MonkeyPatch, cache: ProcessCache) -> None:
    monkeypatch.setattr(mixed_action_cache, "get_process_cache", lambda: cache)
    monkeypatch.setattr(source_cylinder_cache, "get_process_cache", lambda: cache)


def _assert_query_retains_only_accounted_d8_rows(ledger: ResourceLedger) -> None:
    # D8 is intentionally reusable for this caller-owned ledger's lifetime;
    # these are canonical table rows, not request-scope scratch allocations.
    retained = tuple(
        owner for owner in ledger.inventory() if owner.entries or owner.nodes
    )
    if not retained:
        assert ledger.entries == ledger.nodes == 0
        return
    assert {owner.name for owner in retained} <= {
        "collatz-physical-d8-local-table",
        "collatz-physical-d8-width-prefix-table",
    }
    assert all(owner.accounting_delta == 0 for owner in retained)
    assert sum(owner.entries for owner in retained) == ledger.entries
    assert sum(owner.nodes for owner in retained) == ledger.nodes


def _cold_production_d68(monkeypatch: pytest.MonkeyPatch) -> ProcessCache:
    cache = ProcessCache(enabled=True)
    _wire_cache(monkeypatch, cache)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        _D68_SOURCE,
        _QUERY_PHYSICAL_TICKS,
        ledger=ledger,
        shared_cache=True,
    )
    assert result.endpoint == collatz_literal(_D68_SOURCE, _QUERY_PHYSICAL_TICKS)
    assert (
        ledger.counters["collatz_physical_temporal_mixed_clock_macro_physical_ticks"]
        == _D68_PHYSICAL_TICKS
    )
    assert (
        ledger.counters.get(
            "collatz_physical_unified_skew_existing_mixed_parent_yields", 0
        )
        == 1
    )
    assert ledger.counters.get("collatz_physical_unified_skew_composed_actions", 0) == 0
    assert ledger.counters["collatz_hashlife_mixed_publications"] == 1
    _assert_query_retains_only_accounted_d8_rows(ledger)
    assert cache.stats().entries > 0
    return cache


def test_d68_complete_action_is_applied_before_any_new_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = _cold_production_d68(monkeypatch)
    try:

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("a warm complete action ran motif discovery")

        monkeypatch.setattr(mixed_clock_macros, "select_mixed_clock_macro", forbidden)
        monkeypatch.setattr(
            temporal_mixed_execution, "select_mixed_clock_macro", forbidden
        )
        monkeypatch.setattr(temporal_run_executor, "select_mixed_macro", forbidden)
        monkeypatch.setattr(
            temporal_unified_skew_execution, "consume_unified_skew_chain", forbidden
        )
        for source in (_D68_SOURCE, _D68_SOURCE + (1 << 68)):
            ledger = ResourceLedger()
            result = compile_collatz_temporal_run_quotient(
                source,
                _D68_PHYSICAL_TICKS,
                ledger=ledger,
                shared_cache=True,
            )
            assert result.endpoint == collatz_literal(source, _D68_PHYSICAL_TICKS)
            assert ledger.counters["collatz_hashlife_mixed_retrieved"] == 1
            assert ledger.counters["collatz_hashlife_mixed_admitted"] == 1
            assert ledger.counters["collatz_hashlife_mixed_applied_hits"] == 1
            assert (
                ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0)
                == 0
            )
            _assert_query_retains_only_accounted_d8_rows(ledger)
        assert cache.stats().entries > 0
    finally:
        cache.reset()


def test_mixed_cache_rejects_wrong_residue_and_width_transport(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = _cold_production_d68(monkeypatch)
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    try:
        with scratch.scope(), CollatzDyadicMacros(ledger, shared_cache=True) as owner:
            exact = lookup_mixed_action(
                owner,
                _D68_SOURCE,
                _QUERY_PHYSICAL_TICKS,
                scratch,
                include_width=True,
            )
            assert exact is not None and exact.width_blank is not None
            transported = _D68_SOURCE + (1 << 68)
            assert (
                lookup_mixed_action(
                    owner,
                    transported,
                    _QUERY_PHYSICAL_TICKS,
                    scratch,
                    include_width=False,
                )
                is not None
            )
            assert (
                lookup_mixed_action(
                    owner,
                    transported,
                    _QUERY_PHYSICAL_TICKS,
                    scratch,
                    include_width=True,
                )
                is None
            )
            wrong_residue = _D68_SOURCE + (1 << 16)
            assert (
                lookup_mixed_action(
                    owner,
                    wrong_residue,
                    _QUERY_PHYSICAL_TICKS,
                    scratch,
                    include_width=False,
                )
                is None
            )
            assert ledger.counters["collatz_hashlife_mixed_inapplicable"] == 2
            assert ledger.counters["collatz_hashlife_mixed_admitted"] == 2
    finally:
        cache.reset()


def test_process_reset_invalidates_a_published_mixed_parent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = _cold_production_d68(monkeypatch)
    cache.reset()
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    try:
        with scratch.scope(), CollatzDyadicMacros(ledger, shared_cache=True) as owner:
            assert (
                lookup_mixed_action(
                    owner,
                    _D68_SOURCE,
                    _QUERY_PHYSICAL_TICKS,
                    scratch,
                    include_width=False,
                )
                is None
            )
            assert ledger.counters["collatz_hashlife_mixed_misses"] == 1
    finally:
        cache.reset()


def test_smaller_horizon_publication_does_not_replace_larger_parent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A horizon-specific action must not evict a better fit at the same key."""
    cache = ProcessCache(enabled=True)
    _wire_cache(monkeypatch, cache)
    try:
        first_ledger = ResourceLedger()
        first = compile_collatz_temporal_run_quotient(
            _D68_SOURCE,
            _D68_PHYSICAL_TICKS,
            ledger=first_ledger,
            shared_cache=True,
            require_mixed_prefix=True,
        )
        assert first.endpoint == collatz_literal(_D68_SOURCE, _D68_PHYSICAL_TICKS)
        assert first_ledger.counters["collatz_hashlife_mixed_publications"] == 1

        shorter_ledger = ResourceLedger()
        shorter = compile_collatz_temporal_run_quotient(
            _D68_SOURCE,
            64,
            ledger=shorter_ledger,
            shared_cache=True,
            require_mixed_prefix=True,
        )
        assert shorter.endpoint == collatz_literal(_D68_SOURCE, 64)
        assert shorter_ledger.counters["collatz_hashlife_mixed_publications"] == 1

        lookup_ledger = ResourceLedger()
        scratch = RunArithmeticWorkspace.for_ledger(lookup_ledger, "collatz_physical")
        with (
            scratch.scope(),
            CollatzDyadicMacros(lookup_ledger, shared_cache=True) as owner,
        ):
            largest_fit = lookup_mixed_action(
                owner,
                _D68_SOURCE,
                _D68_PHYSICAL_TICKS,
                scratch,
                include_width=False,
            )
            assert largest_fit is not None
            assert largest_fit.physical_ticks == _D68_PHYSICAL_TICKS
    finally:
        cache.reset()


def test_full_bucket_reports_smaller_candidate_as_pruned() -> None:
    def record(steps: int, source: int) -> tuple[int, ...]:
        values = [0] * 17
        values[0] = steps
        values[8] = 1
        values[12] = source
        return tuple(values)

    records = tuple(record(1000 - 10 * index, index + 1) for index in range(8))
    assert len(records) == MAX_RECORDS_PER_PREFIX

    retained, disposition = merge_mixed_action_records(records, record(1, 99))

    assert retained is records
    assert disposition == "pruned"


def test_unissued_mixed_payload_still_checks_exact_gain(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = _cold_production_d68(monkeypatch)
    source_prefix = (_D68_SOURCE & ((1 << 16) - 1),)
    with cache.acquire(
        "collatz-mixed-action-index",
        mixed_clock_macros.MIXED_ACTION_CACHE_VERSION,
        source_prefix,
    ) as lease:
        bucket = mixed_clock_macros.read_mixed_action_cache_bucket(lease)
    assert is_exact_object_tuple(bucket) and bucket
    first = bucket[0]
    assert is_exact_object_tuple(first) and len(first) == 17
    assert all(type(value) is int for value in first)
    first_record = cast(tuple[int, ...], first)
    changed = list(first_record)
    changed[2] += 1 << changed[0]

    with pytest.raises(ValueError, match="differs from its action"):
        mixed_clock_macros.restore_mixed_cache_payload(
            _D68_SOURCE, tuple(changed), include_width=False
        )
    with pytest.raises(ValueError, match="foreign cache lease"):
        mixed_clock_macros.restore_mixed_cache_payload(
            _D68_SOURCE,
            first_record,
            include_width=False,
            cache_lease=cast(CacheLease, object()),
        )

    cache.reset()


def test_optional_publication_preflights_and_uses_the_issued_source_residue(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    with scratch.scope(), BoundaryActionTemplateMemo(ledger) as templates:
        macro = mixed_clock_macros.select_mixed_clock_macro(
            _D68_SOURCE,
            _QUERY_PHYSICAL_TICKS,
            templates=templates,
        )
        assert macro is not None

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("disabled retention performed cache-only work")

        with monkeypatch.context() as no_cache:
            no_cache.setattr(
                mixed_action_cache,
                "get_process_cache",
                lambda: ProcessCache(enabled=False),
            )
            no_cache.setattr(
                mixed_action_cache,
                "validate_mixed_cache_publication",
                forbidden,
            )
            with CollatzDyadicMacros(ledger, shared_cache=True) as owner:
                assert not remember_mixed_action(owner, macro, scratch)

        def forbidden_inverse(_action: DyadicTerminalFieldAction) -> int:
            raise AssertionError("publication recomputed the modular inverse")

        cache = ProcessCache(enabled=True)
        with monkeypatch.context() as enabled_cache:
            enabled_cache.setattr(
                mixed_action_cache, "get_process_cache", lambda: cache
            )
            enabled_cache.setattr(
                DyadicTerminalFieldAction,
                "source_residue",
                property(forbidden_inverse),
            )
            with CollatzDyadicMacros(ledger, shared_cache=True) as owner:
                assert remember_mixed_action(owner, macro, scratch)
        cache.reset()


def test_512_symbol_cache_parent_restores_before_any_child_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = ProcessCache(enabled=True)
    _wire_cache(monkeypatch, cache)
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    motif = (1, 0)
    repetitions = 256
    with scratch.scope(), BoundaryActionTemplateMemo(ledger) as templates:
        action = templates.get(MixedParityMotif(motif), repetitions)[0]
        source = action.source_residue + (5 << action.steps)
        macro = mixed_clock_macros.select_mixed_clock_macro(
            source,
            768,
            templates=templates,
        )
        assert macro is not None
        assert macro.normalized_symbols == 512
        assert macro.physical_ticks == 768
        with CollatzDyadicMacros(ledger, shared_cache=True) as owner:
            assert remember_mixed_action(owner, macro, scratch)
    assert ledger.entries == ledger.nodes == 0

    try:

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("the 512-symbol parent was not reused")

        monkeypatch.setattr(mixed_clock_macros, "select_mixed_clock_macro", forbidden)
        monkeypatch.setattr(
            temporal_mixed_execution, "select_mixed_clock_macro", forbidden
        )
        monkeypatch.setattr(temporal_run_executor, "select_mixed_macro", forbidden)
        receiving_ledger = ResourceLedger()
        result = compile_collatz_temporal_run_quotient(
            source,
            768,
            ledger=receiving_ledger,
            shared_cache=True,
        )
        assert result.endpoint == collatz_literal(source, 768)
        assert receiving_ledger.counters["collatz_hashlife_mixed_retrieved"] == 1
        assert receiving_ledger.counters["collatz_hashlife_mixed_applied_hits"] == 1
        assert (
            receiving_ledger.counters.get(
                "collatz_physical_temporal_d8_discovery_symbols", 0
            )
            == 0
        )
        assert receiving_ledger.entries == receiving_ledger.nodes == 0
    finally:
        cache.reset()


def test_disabled_process_cache_is_reported_as_bypass(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = ProcessCache(enabled=False)
    _wire_cache(monkeypatch, cache)
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    with scratch.scope(), BoundaryActionTemplateMemo(ledger) as templates:
        action = templates.get(MixedParityMotif((0, 1)), 8)[0]
        source = action.source_residue + (5 << action.steps)
        macro = mixed_clock_macros.select_mixed_clock_macro(
            source, 24, templates=templates
        )
        assert macro is not None
        with CollatzDyadicMacros(ledger, shared_cache=True) as owner:
            assert not remember_mixed_action(owner, macro, scratch)
            assert (
                lookup_mixed_action(
                    owner,
                    macro.source,
                    macro.physical_ticks,
                    scratch,
                    include_width=False,
                )
                is None
            )
            assert ledger.counters["collatz_hashlife_mixed_bypasses"] == 2
    assert ledger.entries == ledger.nodes == 0
    cache.reset()
