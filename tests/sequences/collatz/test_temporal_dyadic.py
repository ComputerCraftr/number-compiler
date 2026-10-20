"""Finite D8 coefficients, physical clocks, and ledger-owned cold discovery."""

from collections.abc import MutableMapping
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8CylinderFrame,
    D8TemporalTable,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def test_complete_d8_source_residues_bind_all_lifts() -> None:
    ledger = ResourceLedger()
    table = D8TemporalTable.for_ledger(ledger)
    for residue in range(256):
        for lift in (1, 7, 1 << 128):
            source = residue + (lift << 8)
            ones, target_origin = table.select(source)
            expected, observed_ones = source, 0
            for _ in range(8):
                bit = expected & 1
                observed_ones += bit
                expected = (3 * expected + 1) >> 1 if bit else expected >> 1
            assert target_origin + 3**ones * lift == expected
            assert ones == observed_ones
    assert len(table.rows) == ledger.entries == 256
    assert ledger.nodes == 256 * table.NODES_PER_ROW
    assert ledger.counters["collatz_physical_temporal_d8_discovery_symbols"] == 2048
    assert ledger.counters["collatz_physical_temporal_d8_table_hits"] == 512
    assert D8TemporalTable.for_ledger(ledger).rows is table.rows
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


def test_d8_rows_live_until_the_last_interleaved_workspace_disposes() -> None:
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
    )

    ledger = ResourceLedger()
    first = CollatzPhysicalImageWorkspace(
        ledger,
        (1 << 160) + 48_233_076_155_686_138_603,
        108,
        retain_chronology=False,
    )
    table = D8TemporalTable.for_ledger(ledger)
    assert len(table.rows) > 0
    initial_rows = len(table.rows)

    second = CollatzPhysicalImageWorkspace(
        ledger,
        (1 << 160) + 48_233_076_155_686_138_603,
        108,
        retain_chronology=False,
    )
    assert D8TemporalTable.for_ledger(ledger).rows is table.rows
    first.dispose()
    assert len(table.rows) == initial_rows

    class DerivedWorkspace(CollatzPhysicalImageWorkspace):
        pass

    derived_lease = object.__new__(DerivedWorkspace)
    derived_lease.ledger = ledger
    object.__setattr__(derived_lease, "_closed", False)
    ledger.register_execution_root(derived_lease)
    second.dispose()
    assert len(table.rows) == initial_rows

    object.__setattr__(derived_lease, "_closed", True)
    from number_compiler.sequences.collatz.physical_boundary_route import (
        release_d8_rows_if_unleased,
    )

    release_d8_rows_if_unleased(ledger, CollatzPhysicalImageWorkspace)
    assert len(table.rows) == 0
    assert len(table.width_prefixes) == 0
    assert ledger.entries == ledger.nodes == 0


def test_target_centering_separates_actions_from_occurrences() -> None:
    table = D8TemporalTable.for_ledger(ResourceLedger())
    rows = [table.select(residue + 256) for residue in range(256)]
    assert len({ones for ones, _origin in rows}) == 9
    assert len(set(rows)) == 127
    # The same centered action must not authorize another source origin.
    first = next(row for row in rows if row[0] == 4)
    other = next(row for row in rows if row[0] == 4 and row != first)
    assert first[1] + 3 ** first[0] != other[1] + 3 ** other[0]


def test_cylinder_transition_composes_without_materializing_midpoints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    table = D8TemporalTable.for_ledger(ResourceLedger())

    def forbidden(frame: D8CylinderFrame) -> int:
        raise AssertionError("transition materialized the full source lift")

    monkeypatch.setattr(D8CylinderFrame, "materialize", forbidden)
    for residue in range(256):
        source = (1 << 1024) + (73 << 8) + residue
        first, h1, _r1, _t1 = table.transition(D8CylinderFrame(source))
        second, h2, _r2, _t2 = table.transition(first)
        assert first.source is second.source
        assert second.consumed == 16
        expected, ones = source, 0
        for _ in range(16):
            bit = expected & 1
            ones += bit
            expected = (3 * expected + 1) >> 1 if bit else expected >> 1
        assert second.origin + second.gain * (source >> 16) == expected
        assert h1 + h2 == ones


def test_frame_residue_tracks_bounded_fiber_without_materializing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    table = D8TemporalTable.for_ledger(ResourceLedger())
    direct = D8CylinderFrame(0x123456789ABCDEF, consumed=16, origin=17, gain=9)
    assert direct.residue(160) == direct.materialize() % 160

    def forbidden(frame: D8CylinderFrame) -> int:
        raise AssertionError("residue probe materialized the high fiber")

    monkeypatch.setattr(D8CylinderFrame, "materialize", forbidden)
    for source in range(1, 257):
        assert D8CylinderFrame(source).residue(160) == source % 160

    source = (1 << 1024) + (73 << 8) + 0xA5
    frame = D8CylinderFrame(source)
    for _ in range(12):
        expected = (frame.origin + frame.gain * (source >> frame.consumed)) % 160
        assert frame.residue(160) == expected
        frame, _ones, _residue, _origin = table.transition(frame)


def test_unobserved_frame_creation_and_advance_skip_f5_residue(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    table = D8TemporalTable.for_ledger(ResourceLedger())

    def forbidden(source: int, consumed: int) -> int:
        raise AssertionError("unrequested frame computed its F5 residue")

    monkeypatch.setattr(
        D8CylinderFrame,
        "_compute_high_fiber_mod5",
        staticmethod(forbidden),
    )
    frame = D8CylinderFrame((1 << 4096) + 0xA5)
    assert object.__getattribute__(frame, "_high_fiber_mod5") is None
    advanced, _ones, _residue, _origin = table.transition(frame)
    assert object.__getattribute__(advanced, "_high_fiber_mod5") is None


@pytest.mark.validation
def test_exhaustive_d16_centered_composition_and_occurrence_counts() -> None:
    table = D8TemporalTable.for_ledger(ResourceLedger())
    translated: set[tuple[int, int]] = set()
    for residue in range(65536):
        source = residue + 65536
        first, h1, _r1, _t1 = table.transition(D8CylinderFrame(source))
        second, h2, _r2, _t2 = table.transition(first)
        endpoint = second.materialize()
        expected, ones = source, 0
        for _ in range(16):
            bit = expected & 1
            ones += bit
            expected = (3 * expected + 1) // 2 if bit else expected // 2
        assert endpoint == expected
        assert ones == h1 + h2
        translated.add((ones, endpoint - 3**ones))
    assert len({ones for ones, _origin in translated}) == 17
    assert len(translated) == 19275


def test_public_astronomical_clock_preserves_earliest_cycle_entry() -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    term = PoweredCollatzTerm(27, 10**12)
    assert term.materialize(max_bits=8) == 4
    assert (
        term.resource_ledger.counters["collatz_physical_temporal_cycle_pump_requests"]
        == 1
    )
    assert (
        term.resource_ledger.counters[
            "collatz_physical_temporal_cycle_pump_repetitions"
        ]
        == (10**12 - 111) // 3
    )
    assert (
        term.resource_ledger.counters.get("source_image_primitive_applications", 0) == 0
    )
    assert term.resource_ledger.peak_nodes < 1000


def test_d8_cold_budget_rejects_before_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import temporal_dyadic

    def forbidden(residue: int) -> tuple[int, int]:
        raise AssertionError("discovery ran before its retained reservation")

    monkeypatch.setattr(temporal_dyadic, "d8_row", forbidden)
    ledger = ResourceLedger(max_cache_entries=0)
    with pytest.raises(BlockContextBudgetExceeded):
        compile_collatz_temporal_run_quotient(27, 64, ledger=ledger)
    assert ledger.entries == ledger.nodes == 0
    assert ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0) == 0


def test_failed_d8_discovery_releases_both_reservations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import temporal_dyadic

    def failed(residue: int) -> tuple[int, int]:
        raise ArithmeticError("cold row failure")

    monkeypatch.setattr(temporal_dyadic, "d8_row", failed)
    ledger = ResourceLedger()
    with pytest.raises(ArithmeticError, match="cold row failure"):
        compile_collatz_temporal_run_quotient(27, 64, ledger=ledger)
    assert ledger.entries == ledger.nodes == 0
    assert ledger.counters["collatz_physical_temporal_d8_discovery_requests"] == 1
    assert ledger.counters["collatz_physical_temporal_d8_discovery_failures"] == 1
    assert ledger.counters["collatz_physical_temporal_d8_discovery_symbols"] == 8
    assert (
        ledger.counters.get("collatz_physical_temporal_d8_table_publications", 0) == 0
    )
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


@pytest.mark.parametrize("seed,entry", [(1, 0), (2, 1), (4, 2), (27, 111)])
@pytest.mark.parametrize("phase,endpoint", [(0, 1), (1, 4), (2, 2)])
def test_d8_preserves_first_cycle_entry_and_every_physical_phase(
    seed: int, entry: int, phase: int, endpoint: int
) -> None:
    repetitions = 10**8
    result = compile_collatz_temporal_run_quotient(
        seed, entry + 3 * repetitions + phase, ledger=ResourceLedger(), include_f5=True
    )
    assert result.endpoint == endpoint
    assert result.cycle_repetitions == repetitions
    assert result.phase == int(phase == 1)


def test_mixed_d8_pumps_preserve_optional_f5_and_reuse_owned_rows() -> None:
    ledger = ResourceLedger()
    first = compile_collatz_temporal_run_quotient(27, 64, ledger=ledger)
    discoveries = ledger.counters["collatz_physical_temporal_d8_discovery_symbols"]
    assert first.endpoint == 1619
    # Border-return composition removes one action from the previous route.
    # Keep the prior six-action work ceiling without pinning its exact shape.
    assert 0 < first.run_actions <= 6
    assert 0 < ledger.counters["collatz_physical_temporal_dyadic_d8_pumps"] <= 4
    assert ledger.counters["collatz_physical_boundary_6305R_macro_actions"] > 0
    second = compile_collatz_temporal_run_quotient(
        27, 64, ledger=ledger, include_f5=True
    )
    assert second.endpoint == first.endpoint
    assert first.normalized_f5 is None and first.physical_f5 is None
    assert second.physical_f5 is not None
    assert second.physical_f5.apply(27) == 1619 % 5
    assert (
        ledger.counters["collatz_physical_temporal_d8_discovery_symbols"] == discoveries
    )


def test_d8_payload_audit_reconstructs_rows_and_rejects_corruption() -> None:
    from number_compiler.resources.payload_audit import audit_registered_payloads

    ledger = ResourceLedger()
    compile_collatz_temporal_run_quotient(27, 64, ledger=ledger)
    table = D8TemporalTable.for_ledger(ledger)
    assert ledger.counters.get("collatz_d8_payload_audit_local_symbols", 0) == 0
    ledger.snapshot()
    assert ledger.counters.get("collatz_d8_payload_audit_local_symbols", 0) == 0
    report = audit_registered_payloads(ledger)
    assert report.unknown_payloads == report.forbidden_future_payloads == 0
    assert ledger.counters["collatz_d8_payload_audit_local_symbols"] == 16 * len(
        table.rows
    )
    residue = next(iter(table.rows))
    ones, target_origin = table.rows[residue]
    with pytest.raises(TypeError, match="write-once"):
        table.rows[residue] = (ones, target_origin + 1)
    assert compile_collatz_temporal_run_quotient(27, 64, ledger=ledger).endpoint == 1619
    # Deliberate private-store corruption remains visible to the independent
    # audit, while supported mapping mutation cannot change canonical rows.
    raw_rows = cast(
        MutableMapping[int, tuple[int, int]],
        object.__getattribute__(table.rows, "_data"),
    )
    raw_rows[residue] = (ones, target_origin + 1)
    corrupted = audit_registered_payloads(ledger)
    assert corrupted.forbidden_future_payloads > 0


def test_rejected_cycle_section_still_counts_endpoint_work() -> None:
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(4, 20, ledger=ledger)
    assert result.endpoint == 1
    assert ledger.counters["collatz_physical_temporal_d8_endpoint_evaluations"] == 1
    assert ledger.counters.get("collatz_physical_temporal_dyadic_d8_pumps", 0) == 0
    assert ledger.counters["collatz_physical_temporal_run_operand_bits"] >= 30


def test_d8_rejects_foreign_and_disposed_row_stores() -> None:
    ledger = ResourceLedger()
    table = D8TemporalTable.for_ledger(ledger)
    table.select(27)
    original = table.rows
    foreign = D8TemporalTable.for_ledger(ResourceLedger())
    foreign.select(27)
    table.rows = foreign.rows
    with pytest.raises(ValueError, match="another resource owner"):
        table.select(27)
    table.rows = original
    with pytest.raises(ValueError, match="dispose requires"):
        ledger.mark_disposed(table.owner)
    disposed = D8TemporalTable.for_ledger(ResourceLedger())
    disposed.ledger.mark_disposed(disposed.owner)
    with pytest.raises(RuntimeError, match="disposed"):
        disposed.select(27)


def test_d8_canonical_rows_reject_all_replacement_operations() -> None:
    table = D8TemporalTable.for_ledger(ResourceLedger())
    row = table.select(27)
    with pytest.raises(TypeError, match="write-once"):
        table.rows.update({27: row})
    with pytest.raises(TypeError, match="cannot be deleted"):
        del table.rows[27]
    with pytest.raises(TypeError, match="cannot be deleted"):
        table.rows.clear()
    assert table.rows.setdefault(27, row) == row
