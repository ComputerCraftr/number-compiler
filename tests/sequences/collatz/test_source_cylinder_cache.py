"""Exact normalized cylinders and measured production cross-source reuse."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.process_cache import clear_process_cache
from number_compiler.resources.temporal_diagnostics import (
    collect_temporal_diagnostics_snapshot,
)
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.physical_images import COLLATZ_PHYSICAL_LAW
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
)
from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary
from number_compiler.sequences.collatz.temporal_dyadic import D8TemporalTable
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)
from tests.support.reference_arithmetic import literal_dyadic_orbit

pytestmark = pytest.mark.usefixtures("isolated_process_cache")


@pytest.mark.parametrize("endpoint", [1, 2])
def test_observed_terminal_action_remains_an_exact_finite_cylinder(
    endpoint: int,
) -> None:
    source = endpoint << 16
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        macros.observe(source, 16, 0, endpoint, anchor=source)
        assert not macros.frontier
        assert macros.ledger.counters["collatz_hashlife_occurrence_publications"] == 1
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        for fiber in (1, 2, 3):
            action = macros.lookup(fiber << 16, 16)
            assert action is not None
            assert action.apply(fiber << 16) == fiber


def test_width_spine_is_source_qualified_when_endpoint_cylinder_transports() -> None:
    clear_process_cache()
    source = (1 << 200) + 931386509544713451
    current = source
    widths = [current.bit_length()]
    odd_steps = 0
    for _ in range(16):
        if current & 1:
            raw = 3 * current + 1
            odd_steps += 1
            widths.append(raw.bit_length())
            current = raw // 2
        else:
            current //= 2
        widths.append(current.bit_length())
    ticks = 16 + odd_steps
    summary = CollatzTapeWidthSummary(
        widths[0],
        widths[-1],
        ticks,
        16,
        odd_steps,
        BlankLedger(
            widths[-1] - widths[0],
            min(widths) - widths[0],
            max(widths) - widths[0],
        ),
    )
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        assert macros.remember(
            source, 16, odd_steps, current, tape_width_summary=summary
        )
        assert macros.ledger.counters["collatz_hashlife_width_spine_publications"] == 1
        exact = macros.lookup_largest_with_width(source, 16, ticks)
        assert exact is not None and exact[1] == summary
        original_maximum = summary.blank.maximum
        object.__setattr__(summary.blank, "maximum", -10_000)
        try:
            with pytest.raises(ValueError):
                macros.lookup_width_summary(source, 16)
        finally:
            object.__setattr__(summary.blank, "maximum", original_maximum)
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        exact = macros.lookup_largest_with_width(source, 16, ticks)
        assert exact is not None and exact[1] == summary
        assert macros.ledger.counters["collatz_hashlife_width_spine_process_hits"] == 1
        assert (
            macros.ledger.counters.get("collatz_hashlife_width_spine_publications", 0)
            == 0
        )
        transported_source = source + (2 << 200)
        transported = macros.lookup_largest_with_width(transported_source, 16, ticks)
        assert transported is not None and transported[0] == exact[0]
        assert transported[1] is None
    clear_process_cache()


def test_warm_complete_germ_skips_discovery_for_another_high_fiber(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (1 << 200) + 931386509544713451
    compile_collatz_temporal_run_quotient(
        source, 1000, ledger=ResourceLedger(), shared_cache=True
    )
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as first:
        cell = first.lookup(source, 128)
        assert cell is not None
    second = CollatzDyadicMacros(ResourceLedger(), shared_cache=True)

    def forbidden(self: D8TemporalTable, source: int) -> None:
        raise AssertionError("warm source germ replayed primitive discovery")

    monkeypatch.setattr(D8TemporalTable, "select", forbidden)
    other = source + (2 << 200)
    reused = second.lookup(other, 128)
    assert reused is not None
    assert reused == cell
    assert reused.apply(other) - cell.apply(source) == cell.multiplier * (2 << 72)
    assert second.ledger.counters["collatz_hashlife_occurrence_process_hits"] == 1
    assert second.ledger.counters["collatz_hashlife_occurrence_transported_hits"] == 1
    assert second.ledger.counters.get("collatz_hashlife_primitive_steps", 0) == 0
    with pytest.raises(ValueError, match="germ differs"):
        reused.apply(other ^ 1)
    clear_process_cache()


def test_production_cross_seed_reuse_reduces_observed_source_work() -> None:
    clear_process_cache()
    observations = []
    for high in (1, 3):
        seed = (high << 200) + 931386509544713451
        term = PoweredCollatzTerm(seed, 1000, shared_cache=True)
        expected = literal_dyadic_orbit(seed, 1000, COLLATZ_PHYSICAL_LAW)[0]
        assert term.materialize(max_bits=1000) == expected
        metrics = term.metrics()
        from number_compiler.resources.metric_collection import collect_ledger_metrics

        assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete
        assert metrics.resource_accounting_mismatch == 0
        observations.append(term.resource_ledger.snapshot().counters)
    cold, warm = observations
    assert cold["collatz_hashlife_max_level"] >= 7
    assert cold["collatz_hashlife_occurrence_publications"] > 1
    assert warm["collatz_hashlife_occurrence_transported_hits"] > 0
    assert warm["collatz_hashlife_occurrence_process_hits"] > 0
    assert (
        warm["collatz_hashlife_primitive_steps"]
        < cold["collatz_hashlife_primitive_steps"]
    )
    assert (
        warm.get("collatz_hashlife_occurrence_exact_hits", 0)
        + warm["collatz_hashlife_occurrence_transported_hits"]
        > 0
    )
    clear_process_cache()


def test_transported_checkpoint_reduces_work_on_same_receiving_seed() -> None:
    source = (1 << 200) + 931386509544713451
    receiving = source + (2 << 200)
    cold = PoweredCollatzTerm(receiving, 1000, shared_cache=False)
    expected = cold.materialize(max_bits=1000)
    producer = PoweredCollatzTerm(source, 1000, shared_cache=True)
    producer.materialize(max_bits=1000)
    warm = PoweredCollatzTerm(receiving, 1000, shared_cache=True)
    assert warm.materialize(max_bits=1000) == expected
    assert (
        warm.resource_ledger.counters["collatz_hashlife_occurrence_transported_hits"]
        > 0
    )
    assert (
        warm.resource_ledger.counters["collatz_physical_temporal_d8_discovery_symbols"]
        + warm.resource_ledger.counters.get(
            "collatz_temporal_root_checkpoint_d8_steps", 0
        )
        < cold.resource_ledger.counters[
            "collatz_physical_temporal_d8_discovery_symbols"
        ]
    )


def test_disabled_shared_cache_retains_original_production_route() -> None:
    term = PoweredCollatzTerm(27, 100, shared_cache=False)
    assert (
        term.materialize(max_bits=1000)
        == literal_dyadic_orbit(27, 100, COLLATZ_PHYSICAL_LAW)[0]
    )
    assert not any(
        key.startswith("collatz_hashlife_") for key in term.resource_ledger.counters
    )


def test_macro_records_are_subject_to_local_resource_admission() -> None:
    clear_process_cache()
    source = (1 << 200) + 931386509544713451
    compile_collatz_temporal_run_quotient(
        source, 1000, ledger=ResourceLedger(), shared_cache=True
    )
    with CollatzDyadicMacros(
        ResourceLedger(max_cache_entries=0), shared_cache=True
    ) as macros:
        with pytest.raises(BlockContextBudgetExceeded):
            macros.lookup(source, 128)
        assert macros.ledger.entries == 0
        assert (
            macros.ledger.counters["collatz_hashlife_occurrence_admission_rejections"]
            == 1
        )
        assert macros.ledger.counters["collatz_hashlife_failed_work"] == 1
        from number_compiler.resources.metric_collection import collect_ledger_metrics

        assert collect_ledger_metrics(macros.ledger).resource_audit_complete
    clear_process_cache()


def test_cache_reset_and_different_width_require_new_admission() -> None:
    clear_process_cache()
    source = (1 << 200) + 931386509544713451
    compile_collatz_temporal_run_quotient(
        source, 1000, ledger=ResourceLedger(), shared_cache=True
    )
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as changed:
        assert changed.lookup(source, 256) is None
        assert not any(
            changed.ledger.counters.get(f"collatz_hashlife_occurrence_{kind}_hits", 0)
            for kind in ("exact", "transported", "local", "process")
        )
    changed_ledger = ResourceLedger()
    changed_result = compile_collatz_temporal_run_quotient(
        source, 128, ledger=changed_ledger, shared_cache=True
    )
    assert (
        changed_result.endpoint
        == literal_dyadic_orbit(source, 128, COLLATZ_PHYSICAL_LAW)[0]
    )
    # The NC11 source-bound 6305 producer may now account for the complete
    # cold path without scalar primitive steps. The changed-width occurrence
    # must still be independently re-admitted after the miss above.
    assert changed_ledger.counters["collatz_physical_boundary_6305R_macro_actions"] > 0
    clear_process_cache()
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as reset:
        assert reset.lookup(source, 128) is None
        assert not any(
            reset.ledger.counters.get(f"collatz_hashlife_occurrence_{kind}_hits", 0)
            for kind in ("exact", "transported", "local", "process")
        )
    reset_ledger = ResourceLedger()
    compile_collatz_temporal_run_quotient(
        source, 1000, ledger=reset_ledger, shared_cache=True
    )
    assert reset_ledger.counters["collatz_physical_boundary_6305R_macro_actions"] > 0
    assert all(item.entries == 0 for item in reset.ledger.inventory() if item.disposed)
    clear_process_cache()


def test_collatz_cli_consumes_shared_source_germ(
    capsys: pytest.CaptureFixture[str],
) -> None:
    import json

    from number_compiler.api import cli

    clear_process_cache()
    for high in (1, 3):
        seed = (high << 200) + 931386509544713451
        assert (
            cli.main(
                ["collatz", "--seed", str(seed), "--nth", "1000", "--format", "json"]
            )
            == 0
        )
        captured = capsys.readouterr()
        assert captured.err == ""
        assert json.loads(captured.out)["value"] == str(
            literal_dyadic_orbit(seed, 1000, COLLATZ_PHYSICAL_LAW)[0]
        )
    clear_process_cache()


@pytest.mark.parametrize(
    "payload", ((1, 0, 2, 0), (1, 0, 3, -1), (True, 0, 3, 0), (1, 0))
)
def test_malformed_shared_occurrence_is_rejected(payload: tuple[object, ...]) -> None:
    from typing import cast

    from number_compiler.resources.process_cache import (
        ImmutableValue,
        get_process_cache,
    )
    from number_compiler.sequences.collatz import source_cylinder_cache

    clear_process_cache()
    with get_process_cache().acquire(
        "collatz-dyadic-occurrence", CollatzDyadicMacros.VERSION, (8, 27)
    ) as lease:
        lease.put_issued(
            ("effect",),
            cast(ImmutableValue, payload),
            source_cylinder_cache._OCCURRENCE_PUBLISHER,
        )
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        with pytest.raises((TypeError, ValueError)):
            macros.lookup(27, 8)
        assert (
            macros.ledger.counters["collatz_hashlife_occurrence_admission_rejections"]
            == 1
        )
        assert macros.ledger.counters["collatz_hashlife_failed_work"] == 1
        assert not any(
            macros.ledger.counters.get(f"collatz_hashlife_occurrence_{kind}_hits", 0)
            for kind in ("exact", "transported", "local", "process")
        )
    clear_process_cache()


def test_public_process_lease_cannot_forge_valid_collatz_occurrence() -> None:
    from number_compiler.resources.process_cache import (
        CacheRecordIssuerMismatch,
        get_process_cache,
    )

    clear_process_cache()
    with get_process_cache().acquire(
        "collatz-dyadic-occurrence", CollatzDyadicMacros.VERSION, (8, 27)
    ) as lease:
        assert lease.put(("effect",), (0, 0, 1, 0))
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        with pytest.raises(CacheRecordIssuerMismatch, match="publisher capability"):
            macros.lookup(27, 8)
        counters = macros.ledger.counters
        assert counters["collatz_hashlife_occurrence_lookups"] == 1
        assert counters["collatz_hashlife_occurrence_admission_rejections"] == 1
        assert counters["collatz_hashlife_failed_work"] == 1
        assert counters.get("collatz_hashlife_gain_construction_operand_bits", 0) == 0
        assert counters["collatz_hashlife_occurrence_process_hits"] == 0
        assert counters["collatz_hashlife_occurrence_exact_hits"] == 0
    clear_process_cache()


def test_powered_cycle_never_expands_normalized_macro_germ(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(self: CollatzDyadicMacros, *args: object, **kwargs: object) -> None:
        raise AssertionError("cycle pump constructed a raw normalized cylinder")

    monkeypatch.setattr(CollatzDyadicMacros, "remember", forbidden)
    seed = 1 << 80
    ticks = 80 + 3 * ((1 << 60) - 40) + 1
    result = compile_collatz_temporal_run_quotient(
        seed, ticks, ledger=ResourceLedger(), shared_cache=True
    )
    assert result.endpoint == 4
    assert result.cycle_repetitions == (1 << 60) - 40


def test_warm_cross_seed_preserves_complete_f5_actions() -> None:
    clear_process_cache()
    low = 931386509544713451
    compile_collatz_temporal_run_quotient(
        (1 << 200) + low,
        1000,
        ledger=ResourceLedger(),
        shared_cache=True,
        include_f5=True,
    )
    other = (3 << 200) + low
    cold = compile_collatz_temporal_run_quotient(
        other,
        1000,
        ledger=ResourceLedger(),
        shared_cache=False,
        include_f5=True,
    )
    warm_ledger = ResourceLedger()
    warm = compile_collatz_temporal_run_quotient(
        other,
        1000,
        ledger=warm_ledger,
        shared_cache=True,
        include_f5=True,
    )
    assert warm_ledger.counters["collatz_hashlife_occurrence_transported_hits"] >= 1
    assert warm.endpoint == cold.endpoint
    assert warm.normalized_f5 == cold.normalized_f5
    assert warm.physical_f5 == cold.physical_f5
    assert warm.normalized_symbols == cold.normalized_symbols
    clear_process_cache()


@pytest.mark.parametrize("max_bytes", [1, 1024])
def test_optional_process_capacity_never_refuses_exact_construction(
    monkeypatch: pytest.MonkeyPatch, max_bytes: int
) -> None:
    from number_compiler.resources.process_cache import ProcessCache
    from number_compiler.sequences.collatz import source_cylinder_cache

    cache = ProcessCache(max_entries=1, max_bytes=max_bytes)
    monkeypatch.setattr(source_cylinder_cache, "get_process_cache", lambda: cache)
    seed = (1 << 200) + 931386509544713451
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        seed, 1000, ledger=ledger, shared_cache=True
    )
    assert result.endpoint == literal_dyadic_orbit(seed, 1000, COLLATZ_PHYSICAL_LAW)[0]
    assert ledger.counters["collatz_hashlife_occurrence_bypasses"] >= 2
    assert ledger.counters["collatz_hashlife_key_operand_bits"] > 0
    assert cache.stats().active_leases == 0
    assert cache.stats().entries == 0


def test_smaller_request_uses_completed_submacro_before_any_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    clear_process_cache()
    source = (1 << 200) + 931386509544713451
    compile_collatz_temporal_run_quotient(
        source, 1000, ledger=ResourceLedger(), shared_cache=True
    )
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        parent = macros.lookup(source, 64)
        assert parent is not None
    other = source + (2 << 200)
    ticks = parent.width + parent.odd_symbols
    expected = literal_dyadic_orbit(other, ticks, COLLATZ_PHYSICAL_LAW)[0]

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("admitted submacro performed cold discovery")

    monkeypatch.setattr(D8TemporalTable, "select", forbidden)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        other, ticks, ledger=ledger, shared_cache=True
    )
    assert result.endpoint == expected
    assert result.normalized_symbols == 64
    assert ledger.counters["collatz_hashlife_occurrence_process_hits"] == 1
    assert ledger.counters["collatz_hashlife_occurrence_transported_hits"] == 1
    assert ledger.counters["collatz_hashlife_occurrence_applied_hits"] == 1
    assert ledger.counters["collatz_hashlife_occurrence_applied_parent_hits"] == 1
    assert ledger.counters["collatz_hashlife_primitive_steps"] == 0
    clear_process_cache()


def test_interior_join_retains_exact_submacro_for_a_changed_high_fiber() -> None:
    from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw

    law = DyadicReturnLaw("normalized-test", "v1", (1, 3), (0, 1), (0, 0))
    root = (1 << 200) + 931386509544713451
    interior = literal_dyadic_orbit(root, 32, law)[0]
    middle, _, first_ones, _, _ = literal_dyadic_orbit(interior, 16, law)
    endpoint, _, second_ones, _, _ = literal_dyadic_orbit(middle, 16, law)

    with CollatzDyadicMacros(ResourceLedger()) as macros:
        macros.observe(
            root,
            32,
            literal_dyadic_orbit(root, 32, law)[2],
            interior,
            anchor=root,
        )
        macros.observe(interior, 16, first_ones, middle, anchor=root)
        macros.observe(middle, 16, second_ones, endpoint, anchor=root)
        cell = macros.lookup(interior, 32)
        assert cell is not None
        other = interior + (2 << 32)
        assert cell.apply(other) == literal_dyadic_orbit(other, 32, law)[0]


def test_transported_prefix_and_extended_requests_skip_cold_child_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    clear_process_cache()
    low = 931386509544713451
    publisher = (1 << 200) + low
    compile_collatz_temporal_run_quotient(
        publisher, 1000, ledger=ResourceLedger(), shared_cache=True
    )
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        parent = macros.lookup(publisher, 64)
        assert parent is not None

    other = (3 << 200) + low
    requests = tuple(parent.width + parent.odd_symbols + extra for extra in (0, 2))
    expected = tuple(
        literal_dyadic_orbit(other, ticks, COLLATZ_PHYSICAL_LAW)[0]
        for ticks in requests
    )
    cold_ledgers = tuple(ResourceLedger() for _ in requests)
    cold = tuple(
        compile_collatz_temporal_run_quotient(
            other, ticks, ledger=ledger, shared_cache=False
        )
        for ticks, ledger in zip(requests, cold_ledgers, strict=True)
    )
    assert tuple(result.endpoint for result in cold) == expected
    assert all(
        ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0) > 0
        for ledger in cold_ledgers
    )

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("warm prefix replayed D8 child discovery")

    monkeypatch.setattr(D8TemporalTable, "select", forbidden)
    warm_ledgers = tuple(ResourceLedger() for _ in requests)
    warm = tuple(
        compile_collatz_temporal_run_quotient(
            other, ticks, ledger=ledger, shared_cache=True
        )
        for ticks, ledger in zip(requests, warm_ledgers, strict=True)
    )
    assert tuple(result.endpoint for result in warm) == expected
    assert all(
        ledger.counters["collatz_hashlife_occurrence_transported_hits"] == 1
        and ledger.counters["collatz_hashlife_occurrence_applied_hits"] == 1
        and ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0)
        == 0
        for ledger in warm_ledgers
    )
    clear_process_cache()


@pytest.mark.parametrize("coordinate", ("gain", "odd_count"))
def test_poisoned_shared_occurrence_gain_is_rejected(coordinate: str) -> None:
    from typing import cast

    from number_compiler.resources.process_cache import (
        ImmutableValue,
        get_process_cache,
    )
    from number_compiler.sequences.collatz import source_cylinder_cache

    clear_process_cache()
    source = (1 << 200) + 931386509544713451
    compile_collatz_temporal_run_quotient(
        source, 1000, ledger=ResourceLedger(), shared_cache=True
    )
    residue = source & ((1 << 128) - 1)
    with get_process_cache().acquire(
        "collatz-dyadic-occurrence", CollatzDyadicMacros.VERSION, (128, residue)
    ) as lease:
        payload = lease.get_issued(
            ("effect",), source_cylinder_cache._OCCURRENCE_PUBLISHER
        )
        assert type(payload) is tuple and len(payload) == 4
        assert all(type(value) is int for value in payload)
        poisoned = list(cast(tuple[int, int, int, int], payload))
        if coordinate == "gain":
            poisoned[2] = int(poisoned[2]) + 1
        else:
            poisoned[0] = 129
        assert lease.put_issued(
            ("effect",),
            cast(ImmutableValue, tuple(poisoned)),
            source_cylinder_cache._OCCURRENCE_PUBLISHER,
        )

    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        before_gain_work = macros.ledger.counters.get(
            "collatz_hashlife_gain_construction_operand_bits", 0
        )
        with pytest.raises(ValueError, match="gain"):
            macros.lookup(source, 128)
        counters = macros.ledger.counters
        assert counters["collatz_hashlife_occurrence_process_hits"] == 0
        assert counters["collatz_hashlife_occurrence_exact_hits"] == 0
        if coordinate == "odd_count":
            assert (
                counters.get("collatz_hashlife_gain_construction_operand_bits", 0)
                == before_gain_work
            )
        assert counters["collatz_hashlife_occurrence_admission_rejections"] == 1
        assert counters["collatz_hashlife_failed_work"] == 1
    clear_process_cache()


def test_frontier_never_composes_across_an_unmatched_shorter_suffix() -> None:
    from number_compiler.hashlife.execution.dyadic_return_records import DyadicReturnLaw

    law = DyadicReturnLaw("normalized-test", "v1", (1, 3), (0, 1), (0, 0))
    seed = (1 << 200) + 931386509544713451
    source = seed
    with CollatzDyadicMacros(ResourceLedger()) as macros:
        for width in (16, 8, 16, 16):
            endpoint, _, ones, _, _ = literal_dyadic_orbit(source, width, law)
            macros.observe(source, width, ones, endpoint, anchor=seed)
            source = endpoint
        assert macros.lookup(seed, 16) is not None
        # The two later D16 blocks start at symbol 24. Neither may be combined
        # with the original D16 across the intervening unmatched D8.
        assert macros.lookup(seed, 32) is None


def test_public_smaller_high_fiber_uses_admitted_prefix_and_reduces_work() -> None:
    clear_process_cache()
    low = 931386509544713451
    publisher = PoweredCollatzTerm((1 << 200) + low, 1000, shared_cache=True)
    publisher.materialize(max_bits=1000)
    receiver = (1 << 80) + low
    warm = PoweredCollatzTerm(receiver, 200, shared_cache=True)
    bypass = PoweredCollatzTerm(receiver, 200, shared_cache=False)
    expected = literal_dyadic_orbit(receiver, 200, COLLATZ_PHYSICAL_LAW)[0]
    assert warm.materialize(max_bits=1000) == expected
    assert bypass.materialize(max_bits=1000) == expected
    counters = warm.resource_ledger.counters
    assert counters["collatz_hashlife_max_level"] == 6
    assert counters["collatz_hashlife_occurrence_applied_hits"] == 1
    assert counters["collatz_hashlife_occurrence_applied_parent_hits"] == 1
    assert (
        counters["collatz_physical_temporal_run_actions"]
        < bypass.resource_ledger.counters["collatz_physical_temporal_run_actions"]
    )
    assert warm.metrics().resource_accounting_mismatch == 0
    clear_process_cache()


def test_warm_occurrence_does_not_rebuild_its_canonical_gain(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import source_cylinder_cache

    clear_process_cache()
    source = (1 << 200) + 931386509544713451
    compile_collatz_temporal_run_quotient(
        source, 1000, ledger=ResourceLedger(), shared_cache=True
    )

    def forbidden(_exponent: int) -> int:
        raise AssertionError("warm occurrence reconstructed its canonical power")

    monkeypatch.setattr(source_cylinder_cache, "_canonical_gain", forbidden)
    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger, shared_cache=True) as macros:
        cell = macros.lookup(source, 128)
        assert cell is not None
        transported = source + (2 << 200)
        assert cell.apply(transported) - cell.apply(source) == cell.multiplier << 73
        assert ledger.counters["collatz_hashlife_gain_process_hits"] == 1
        assert (
            ledger.counters.get("collatz_hashlife_gain_construction_operand_bits", 0)
            == 0
        )
    assert ledger.entries == 0
    before = dict(ledger.counters)
    record = collect_temporal_diagnostics_snapshot(ledger).macrocells[0]
    assert record.gain_process_hits == 1
    assert record.gain_construction_operand_bits == 0
    assert record.gain_key_operand_bits is not None
    assert dict(ledger.counters) == before
    clear_process_cache()


def test_public_occurrence_has_no_gain_evidence_bypass() -> None:
    from inspect import signature

    from number_compiler.sequences.collatz.source_cylinder_types import (
        CollatzDyadicOccurrence,
    )

    with pytest.raises(ValueError, match="centered coefficients"):
        CollatzDyadicOccurrence(8, 0, 0, 0, 2)
    assert "_gain_evidence" not in signature(CollatzDyadicOccurrence).parameters


def test_local_gain_and_occurrence_memos_reject_malformed_records() -> None:
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        _CanonicalGain,
    )

    with CollatzDyadicMacros(ResourceLedger()) as macros:
        macros.gains[0] = 1  # type: ignore[assignment]
        with pytest.raises(ValueError, match="local canonical gain"):
            macros._gain(0)
        macros.gains[0] = _CanonicalGain(0)
        assert macros._gain(0).multiplier == 1

        gain = macros.gains[0]
        object.__setattr__(gain, "multiplier", 2)
        with pytest.raises(ValueError, match="local canonical gain"):
            macros._gain(0)
        object.__setattr__(gain, "multiplier", 1)
        assert macros._gain(0).multiplier == 1

        macros.occurrences[8, 27] = ("not-an-occurrence", 0)  # type: ignore[assignment]
        with pytest.raises(ValueError, match="local occurrence"):
            macros.lookup(27, 8)
        assert macros.ledger.counters["collatz_hashlife_occurrence_local_hits"] == 0
        assert (
            macros.ledger.counters["collatz_hashlife_occurrence_admission_rejections"]
            == 1
        )


@pytest.mark.parametrize("node_budget", (0, 1))
def test_local_gain_seal_obeys_node_budget_and_cleanup(node_budget: int) -> None:
    ledger = ResourceLedger(max_nodes=node_budget)
    with CollatzDyadicMacros(ledger) as macros:
        assert macros._gain(7).multiplier == 2187
        assert len(macros.gains) == node_budget
        assert ledger.nodes == node_budget
        assert ledger.counters["collatz_hashlife_gain_bypasses"] == 1 - node_budget
    assert ledger.nodes == ledger.entries == 0


def test_local_occurrence_cache_rejects_mutated_action_or_publisher_fiber() -> None:
    source, width, ones, endpoint = 27, 8, 7, 242
    with CollatzDyadicMacros(ResourceLedger()) as macros:
        assert macros.remember(source, width, ones, endpoint)
        key = (width, source)
        occurrence, publisher_fiber, snapshot = macros.occurrences[key]

        # The exact Collatz occurrence is frozen, but object.__setattr__ can
        # still change its centered offset while keeping a structurally valid
        # affine map. A cache hit must compare the original publication seal.
        object.__setattr__(occurrence, "target_origin", occurrence.target_origin + 1)
        with pytest.raises(ValueError, match="binding was changed"):
            macros.lookup(source, width)

        # Restore the action and independently exercise mutation of the cached
        # publisher fiber, which classifies exact versus transported reuse.
        object.__setattr__(occurrence, "target_origin", snapshot[3])
        macros.occurrences[key] = (occurrence, publisher_fiber + 1, snapshot)
        with pytest.raises(ValueError, match="binding was changed"):
            macros.lookup(source, width)


def test_gain_process_payload_is_bound_to_its_exponent() -> None:
    from typing import cast

    from number_compiler.resources.process_cache import (
        ImmutableValue,
        get_process_cache,
    )
    from number_compiler.sequences.collatz import source_cylinder_cache

    clear_process_cache()
    with get_process_cache().acquire(
        "collatz-power-of-three", CollatzDyadicMacros.GAIN_VERSION, (0,)
    ) as lease:
        assert lease.put_issued(
            ("gain",),
            cast(ImmutableValue, (1, 1)),
            source_cylinder_cache._GAIN_PUBLISHER,
        )
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        with pytest.raises(ValueError, match="cache is malformed"):
            macros._gain(0)
        assert macros.ledger.counters["collatz_hashlife_gain_process_hits"] == 0
    clear_process_cache()


@pytest.mark.parametrize("failure_kind", ("issuer", "value"))
def test_remember_counts_canonical_gain_admission_failure(
    failure_kind: str,
) -> None:
    from typing import cast

    from number_compiler.resources.process_cache import (
        CacheRecordIssuerMismatch,
        ImmutableValue,
        get_process_cache,
    )
    from number_compiler.sequences.collatz import source_cylinder_cache

    clear_process_cache()
    with get_process_cache().acquire(
        "collatz-power-of-three", CollatzDyadicMacros.GAIN_VERSION, (0,)
    ) as lease:
        if failure_kind == "issuer":
            assert lease.put(("gain",), (0, 1))
        else:
            assert lease.put_issued(
                ("gain",),
                cast(ImmutableValue, (1, 3)),
                source_cylinder_cache._GAIN_PUBLISHER,
            )

    expected_error = (
        CacheRecordIssuerMismatch if failure_kind == "issuer" else ValueError
    )
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        with pytest.raises(expected_error):
            macros.remember(27, 8, 0, 0)
        counters = macros.ledger.counters
        assert counters["collatz_hashlife_occurrence_admission_rejections"] == 1
        assert counters["collatz_hashlife_failed_work"] == 1
        assert counters["collatz_hashlife_gain_bypasses"] == 0
        assert counters["collatz_hashlife_occurrence_publications"] == 0
    clear_process_cache()


def test_closed_macro_owner_rejects_reuse_without_mutating_counters() -> None:
    macros = CollatzDyadicMacros(ResourceLedger())
    with macros:
        assert macros.lookup(27, 8) is None
    before = dict(macros.ledger.counters)
    with pytest.raises(RuntimeError, match="closed"):
        macros.applied()
    with pytest.raises(RuntimeError, match="closed"):
        macros.lookup(27, 8)
    with pytest.raises(RuntimeError, match="closed"):
        macros.__enter__()
    assert macros.ledger.counters == before
    assert macros.ledger.entries == 0


def test_dyadic_macro_close_attempts_every_store_and_retries_failed_owner(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    macros = CollatzDyadicMacros(ledger)
    original = macros.occurrences.dispose
    calls = 0

    def fail_once() -> None:
        nonlocal calls
        calls += 1
        if calls == 1:
            raise RuntimeError("injected occurrence disposal failure")
        original()

    monkeypatch.setattr(macros.occurrences, "dispose", fail_once)
    with pytest.raises(RuntimeError, match="occurrence disposal failure"):
        macros.close()
    assert macros._closed
    assert not macros.occurrences._disposed
    assert macros.width_spines._disposed
    assert macros.gains._disposed
    assert macros.frontier._disposed

    macros.close()
    assert macros.occurrences._disposed
    assert ledger.entries == ledger.nodes == 0


def test_large_width_residue_checks_do_not_build_width_sized_masks() -> None:
    from number_compiler.sequences.collatz.source_cylinder_types import (
        CollatzDyadicOccurrence,
    )

    width = 1 << 100
    occurrence = CollatzDyadicOccurrence(width, 27, 0, 0, 1)
    assert occurrence.apply(27) == 0
    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger) as macros:
        assert macros.remember(27, width, 0, 0)
        remembered = macros.lookup(27, width)
        assert remembered is not None
        assert remembered.apply(27) == 0
        assert ledger.counters["collatz_hashlife_key_operand_bits"] == 2 * (
            (27).bit_length() + width.bit_length()
        )
