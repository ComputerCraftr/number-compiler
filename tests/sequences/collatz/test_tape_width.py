"""Exact source-bound width summaries carried by powered Collatz routes."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)
from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def test_width_summary_composes_exact_zero_and_one_run_envelopes() -> None:
    zero = compile_collatz_temporal_run_quotient(
        1 << 9, 9, ledger=ResourceLedger(), include_width_spine=True
    ).tape_width_summary
    assert zero is not None
    assert (
        zero.source_width,
        zero.target_width,
        zero.physical_ticks,
        zero.normalized_symbols,
        zero.odd_steps,
        zero.blank,
    ) == (10, 1, 9, 9, 0, BlankLedger(-9, -9, 0))

    one = compile_collatz_temporal_run_quotient(
        (1 << 32) - 1,
        64,
        ledger=ResourceLedger(),
        include_width_spine=True,
    ).tape_width_summary
    assert one is not None
    endpoint = 3**32 - 1
    assert (
        one.source_width,
        one.target_width,
        one.physical_ticks,
        one.normalized_symbols,
        one.odd_steps,
        one.blank,
    ) == (
        32,
        endpoint.bit_length(),
        64,
        32,
        32,
        BlankLedger(endpoint.bit_length() - 32, 0, endpoint.bit_length() - 31),
    )


def test_unpaired_odd_half_step_is_in_the_width_summary() -> None:
    result = compile_collatz_temporal_run_quotient(
        11, 1, ledger=ResourceLedger(), include_width_spine=True
    )
    summary = result.tape_width_summary
    assert summary is not None
    assert (result.endpoint, summary.physical_ticks, summary.odd_steps) == (34, 1, 1)
    assert summary.normalized_symbols == 0
    assert summary.blank == BlankLedger(2, 0, 2)


def test_pinned_cycle_summary_is_powered_and_source_bound() -> None:
    workspace = CollatzPhysicalImageWorkspace(
        ResourceLedger(),
        1,
        1002,
        retain_chronology=False,
        include_width_spine=True,
    )
    summary = workspace.tape_width_summary
    assert type(summary) is CollatzTapeWidthSummary
    assert (
        summary.source_width,
        summary.target_width,
        summary.physical_ticks,
        summary.normalized_symbols,
        summary.odd_steps,
        summary.blank,
    ) == (1, 1, 1002, 668, 334, BlankLedger(0, 0, 2))


def test_unrequested_d8_width_spine_stays_absent_and_does_no_prefix_work() -> None:
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(27, 64, ledger=ledger)
    assert result.tape_width_summary is None
    assert (
        ledger.counters.get("collatz_physical_temporal_d8_width_prefix_discoveries", 0)
        == 0
    )


def test_requested_d8_width_spine_matches_every_physical_boundary() -> None:
    seed, ticks = 27, 64
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        seed, ticks, ledger=ledger, include_width_spine=True
    )
    summary = result.tape_width_summary
    assert summary is not None
    widths = [seed.bit_length()]
    current = seed
    for _ in range(ticks):
        current = 3 * current + 1 if current & 1 else current // 2
        widths.append(current.bit_length())
    assert current == result.endpoint
    assert summary.blank.delta == widths[-1] - widths[0]
    assert summary.blank.minimum == min(widths) - widths[0]
    assert summary.blank.maximum == max(widths) - widths[0]
    assert ledger.counters["collatz_physical_temporal_d8_width_prefix_discoveries"] > 0


def test_clock_request_after_an_ordinary_image_does_not_rebuild_width_spine() -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    term = PoweredCollatzTerm(27, 64)
    assert term.materialize(max_bits=100) > 0
    workspace = term._workspace
    assert workspace is not None
    term.s_arithmetic_clock()
    assert term._workspace is workspace
    assert workspace.tape_width_summary is None


def test_workspace_seal_rejects_mutated_summary_geometry() -> None:
    workspace = CollatzPhysicalImageWorkspace(
        ResourceLedger(),
        1,
        1002,
        retain_chronology=False,
        include_width_spine=True,
    )
    summary = workspace.tape_width_summary
    assert type(summary) is CollatzTapeWidthSummary
    object.__setattr__(summary, "target_width", 2)
    try:
        with pytest.raises(ValueError):
            _ = workspace.tape_width_summary
    finally:
        object.__setattr__(summary, "target_width", 1)


@pytest.mark.parametrize("seed,minimum,maximum", ((1, 0, 2), (4, -2, 0), (2, -1, 1)))
def test_huge_cycle_width_has_bounded_work_and_releases_its_publication(
    seed: int, minimum: int, maximum: int
) -> None:
    from number_compiler.resources.payload_audit import audit_registered_payloads

    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(
        ledger,
        seed,
        10**12 + 2,
        retain_chronology=False,
        include_width_spine=True,
    )
    try:
        summary = workspace.tape_width_summary
        assert summary is not None
        assert summary.blank == BlankLedger(0, minimum, maximum)
        assert ledger.counters["collatz_physical_tape_width_repeat_operations"] == 1
        assert ledger.counters.get("collatz_physical_tape_width_compositions", 0) == 0
        report = audit_registered_payloads(ledger)
        assert report.unknown_payloads == 0
        assert report.forbidden_future_payloads == 0
    finally:
        workspace.dispose()
    assert ledger.entries == ledger.nodes == 0
    with pytest.raises(ValueError):
        _ = workspace.tape_width_summary
