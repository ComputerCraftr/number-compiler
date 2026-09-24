"""Independent checks of the chronology-erasing physical Collatz cutover."""

from __future__ import annotations

from random import Random

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.temporal_diagnostics import (
    collect_temporal_diagnostics_snapshot,
)
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)


def _literal(seed: int, steps: int) -> tuple[int, tuple[int, ...]]:
    value = seed
    branches: list[int] = []
    for _ in range(steps):
        bit = value % 2
        branches.append(bit)
        value = 3 * value + 1 if bit else value // 2
    return value, tuple(branches)


def test_saturated_noncycle_support_still_supplies_demanded_branch_segments() -> None:
    rng = Random(0xC011A72)
    seed = (1 << 320) + rng.getrandbits(256) | 1
    steps = 257
    expected, branches = _literal(seed, steps)
    workspace = CollatzPhysicalImageWorkspace(
        ResourceLedger(), seed, steps, retain_chronology=False
    )
    assert workspace.endpoint() == expected
    actual: list[int] = []
    for start, width, word in workspace.segments():
        assert start == len(actual)
        assert 0 < width <= workspace.MAX_LEAF_STEPS
        actual.extend((word >> position) & 1 for position in range(width))
    assert tuple(actual) == branches


def test_saturated_cycle_boundary_keeps_exact_branch_stream() -> None:
    seed = 27
    steps = 257
    expected, branches = _literal(seed, steps)
    workspace = CollatzPhysicalImageWorkspace(
        ResourceLedger(), seed, steps, retain_chronology=False
    )
    assert workspace.endpoint() == expected
    actual: list[int] = []
    for start, width, word in workspace.segments():
        assert start == len(actual)
        actual.extend((word >> position) & 1 for position in range(width))
    assert tuple(actual) == branches


def test_metrics_audit_does_not_recompose_an_entire_growing_prefix() -> None:
    rng = Random(0x5A7)
    audit_bit_work: list[int] = []
    for steps in (512, 1024):
        seed = (1 << (steps + 64)) + rng.getrandbits(steps) | 1
        term = PoweredCollatzTerm(seed, steps)
        expected, _ = _literal(seed, steps)
        assert term.digit(0) == expected & 1
        collect_ledger_metrics(term._ledger)
        audit_bit_work.append(
            term._ledger.counters.get("dyadic_payload_audit_operand_bits", 0)
        )

    # A bounded independent leaf audit is allowed and charged. Rebuilding one
    # ever-wider exact prefix per physical tick grows by about 4x here, while
    # a balanced bounded-leaf audit grows by about 2x.
    assert audit_bit_work[1] <= 3 * audit_bit_work[0] + 20_000


def test_cli_diagnostics_snapshot_does_not_trigger_payload_reconstruction() -> None:
    seed = (1 << 320) + 931_386_509_544_713_451
    term = PoweredCollatzTerm(seed, 257)
    assert term.digit(0) in (0, 1)
    before = dict(term._ledger.counters)
    collect_temporal_diagnostics_snapshot(term._ledger)
    assert term._ledger.counters == before


def test_same_low_cylinder_with_different_high_fibers_keeps_source_authority() -> None:
    steps = 129
    low = (1 << 120) + 931_386_509_544_713_451
    high = low + (1 << (steps + 40))
    first = PoweredCollatzTerm(low, steps)
    second = PoweredCollatzTerm(high, steps)
    first_expected, first_word = _literal(low, steps)
    second_expected, second_word = _literal(high, steps)
    assert first_word == second_word
    assert first_expected != second_expected
    assert first.digit(first.width() - 1) == (first_expected >> (first.width() - 1)) & 1
    assert (
        second.digit(second.width() - 1)
        == (second_expected >> (second.width() - 1)) & 1
    )
