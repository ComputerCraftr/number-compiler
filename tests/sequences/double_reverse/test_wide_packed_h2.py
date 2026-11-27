"""Physical and lifecycle checks for the bounded packed H2 candidate."""

from __future__ import annotations

import pytest

import number_compiler.arithmetic.carry.reflected_h_power as reflected
from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import arithmetic_carry as keys


@pytest.mark.parametrize("generation", (256, 257))
def test_wide_candidate_preserves_physical_endpoint_and_skips_cones(
    generation: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    seed = 10**128 + 908010
    expected = seed
    for _ in range(generation):
        expected = 2 * int(str(expected)[::-1])

    def refuse_cone(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("the packed candidate constructed an H cone")

    monkeypatch.setattr(reflected, "_PACKED_H2_MIN_GENERATION", 256)
    monkeypatch.setattr(reflected, "CarrySpacetimePower", refuse_cone)
    ledger = ResourceLedger()
    owner = ledger.register("packed-h2-test", "scratch")
    arena = LedgerSLPArena(ledger, "packed-h2-output", "grammar")
    try:
        root = reflected.padded_h_publish(
            seed, generation, 2, arena=arena, scratch_owner=owner, max_state_bits=4096
        )
        actual = int("".join(str(digit) for digit in arena.materialize(root)))
        assert actual == expected
        assert (
            ledger.counters[keys.REFLECTED_H_PACKED_ROW_EVALUATIONS]
            == (generation - 1) // 2
        )
        assert ledger.counters[keys.REFLECTED_H_PACKED_ROW_OPERAND_BITS] > 0
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


def test_short_ring_matches_direct_centered_stencil() -> None:
    from number_compiler.arithmetic.carry.decimal_ring_action import centered_short_ring
    from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell

    for first in range(10):
        for second in range(10):
            source = (first, second)
            current = source
            for steps in range(31):
                assert centered_short_ring(source, 2, steps) == current
                assert centered_short_ring(current, 5, steps) == source
                current = (
                    stencil_cell(current[1], current[0], current[1]),
                    stencil_cell(current[0], current[1], current[0]),
                )


@pytest.mark.parametrize("steps", (64, 2048))
def test_short_ring_cone_consumes_complete_repeat_without_packed_rows(
    steps: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    import number_compiler.sequences.double_reverse.temporal_carry_spacetime as temporal
    from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell

    def refuse_packed(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("short-ring action constructed packed rows")

    monkeypatch.setattr(temporal, "_SHORT_RING_MIN_STEPS", 64)
    monkeypatch.setattr(temporal, "publish_packed_diagonal", refuse_packed)
    ledger = ResourceLedger()
    owner = ledger.register("short-ring-test", "scratch")
    arena = LedgerSLPArena(ledger, "short-ring-output", "grammar")
    try:
        root = arena.repeat(arena.word((1, 6)), 2 * steps)
        result = temporal.try_source_bound_square_cone(arena, root, steps, owner)
        assert result is not None
        pair = (1, 6)
        for _ in range(steps):
            pair = (
                stencil_cell(pair[1], pair[0], pair[1]),
                stencil_cell(pair[0], pair[1], pair[0]),
            )
        phase = steps % 2
        expected = pair[phase:] + pair[:phase]
        assert arena.materialize(result) == expected * steps
        assert ledger.counters["double_reverse_f_modular_ring_powers"] == 1
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)
