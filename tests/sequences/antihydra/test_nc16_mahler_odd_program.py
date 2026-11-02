"""Source-bound Mahler program tests; ledger is NOT fractional safety."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.antihydra.mahler_border_identity import (
    MahlerOddMotifSignature,
)
from number_compiler.sequences.antihydra.mahler_mixed_harmonic_ring import (
    MahlerMixedOddHarmonicRing,
)
from number_compiler.sequences.antihydra.mahler_odd_macro import MahlerOddToOddAction
from number_compiler.sequences.antihydra.mahler_odd_program import (
    compile_mahler_odd_program,
)
from tests.support.mahler_harmonic_reference import (
    mapping as _mapping,
)
from tests.support.mahler_harmonic_reference import (
    source_for_motif,
)


def _scalar(
    source: int, max_events: int, max_extent: int = 4096
) -> tuple[int, int, int, int]:
    balance = 0
    clock = 0
    events = 0
    while events < max_events:
        a = ((3 * source + 1) & -(3 * source + 1)).bit_length() - 1
        if clock + a > max_extent or balance + min(0, 3 - a) < 0:
            break
        source = 3 ** (a - 1) * (3 * source + 1) // (1 << a)
        balance += 3 - a
        clock += a
        events += 1
    return source, events, clock, balance


@pytest.mark.parametrize("source", range(1, 200, 2))
def test_persistent_odd_seam_exact_against_scalar(source: int) -> None:
    program = compile_mahler_odd_program(source, max_events=24, source_gate_bits=0)
    expected = _scalar(source, 24)
    assert (
        program.endpoint,
        program.emitted_events,
        program.ending_clock,
        program.ending_balance,
    ) == expected
    assert program.source_certified and not program.physical_scheduler_replaced
    assert not program.fractional_safety_claim
    for frag in program.fragments:
        assert frag.source % frag.source_modulus == frag.source_residue
        assert frag.balance_after == 3 * frag.index_after - frag.clock_after
        assert frag.balance_before + frag.ledger_prefix_minimum >= 0


@pytest.mark.parametrize("word", [(1, 2), (1, 1, 2), (1, 2, 1), (2, 3)])
def test_persistent_mixed_run_reuses_one_compressed_source_fragment(
    word: tuple[int, ...],
) -> None:
    copies = 128
    source = source_for_motif(word, copies)
    program = compile_mahler_odd_program(
        source,
        max_events=len(word) * copies,
        max_extent=4096,
        include_carry_harmonics=True,
    )
    assert program.emitted_events == copies * len(word)
    assert len(program.fragments) == 1
    assert program.avoided_scalar_event_issues == copies * len(word) - 1
    frag = program.fragments[0]
    assert frag.repetitions * len(frag.motif) == program.emitted_events
    assert frag.carry_harmonics is not None
    q_harmonics = _mapping(frag.carry_harmonics["q_temporal_harmonics"])
    assert set(q_harmonics) == {"2", "3", "5", "6", "10", "64"}
    assert program.endpoint == _scalar(source, program.emitted_events)[0]
    assert frag.fractional_guard_empty is True


def test_fragment_rejects_same_weight_action_with_different_ordered_motif() -> None:
    source = source_for_motif((1, 3), 2)
    program = compile_mahler_odd_program(
        source,
        max_events=4,
        max_motif_events=2,
        source_gate_bits=0,
    )
    assert len(program.fragments) == 1
    fragment = program.fragments[0]
    assert fragment.motif == (1, 3)

    reordered = MahlerOddToOddAction.run(2).then(MahlerOddToOddAction.run(2))
    assert reordered.odd_events == len(fragment.motif)
    assert reordered.extent == sum(fragment.motif)
    with pytest.raises(ValueError, match="ordered motif"):
        replace(fragment, motif_action=reordered)
    object.__setattr__(fragment, "motif_action", reordered)
    with pytest.raises(ValueError, match="binding is stale"):
        program.source_at_tick(fragment.clock_before + 2)


def test_any_forged_harmonic_capacity_is_refused_at_creation() -> None:
    signature = MahlerOddMotifSignature((1, 2))
    ring = MahlerMixedOddHarmonicRing.from_source(
        source_for_motif((1, 2), 8), signature
    )
    with pytest.raises(ValueError, match="capacity"):
        replace(ring, capacity=ring.capacity + 1)
    with pytest.raises(ValueError, match="defect"):
        replace(ring, defect=ring.defect + 2)
    with pytest.raises(ValueError):
        replace(ring, source=ring.source + 2)
    with pytest.raises(ValueError):
        replace(ring, macro_identity=MahlerOddMotifSignature((2, 1)).identity)


def test_early_ledger_failure_and_unsupported_clock_are_not_silently_skipped() -> None:
    x = 5  # a=v2(16)=4, first odd-event ledger delta 3-4<0
    r = compile_mahler_odd_program(x, max_events=50)
    assert r.emitted_events == 0
    assert r.stop_reason == "ledger_barrier_before_next_event"
    with pytest.raises(ValueError):
        compile_mahler_odd_program(7, index=5, clock=2, balance=0)
    with pytest.raises(ValueError):
        compile_mahler_odd_program(8)


def test_program_rejects_unbounded_source_and_conflicting_budget_values() -> None:
    oversized = (1 << 65_536) | 1
    with pytest.raises(BlockContextBudgetExceeded):
        compile_mahler_odd_program(oversized)
    with pytest.raises(ValueError):
        compile_mahler_odd_program(7, max_extent=4097)
    with pytest.raises(ValueError):
        compile_mahler_odd_program(7, source_gate_bits=65_537)


def test_ledger_barrier_inside_repeated_mixed_word_keeps_safe_partial_prefix() -> None:
    # Each (1,6) motif begins with +2 ledger units then loses 3.  Starting
    # with zero balance admits the first event but not the second event.
    x = source_for_motif((1, 6), 24)
    assert x.bit_length() >= 96
    program = compile_mahler_odd_program(x, max_events=48)
    assert program.emitted_events == 1
    assert program.stop_reason == "ledger_barrier_before_next_event"
    assert program.ending_balance == 2
    assert program.fragments[0].motif == (1,)
    assert program.endpoint == _scalar(x, 48)[0]
