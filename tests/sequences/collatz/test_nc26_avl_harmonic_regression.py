"""Focused source guards for restored Collatz AVL and harmonic paths."""

from __future__ import annotations

from dataclasses import replace

import pytest

from devtools.verification.oracles.sequence_arithmetic import collatz_literal
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as metric_keys
from number_compiler.sequences.collatz.border_harmonic_ring import (
    PeriodicTail6305Ring,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    select_border_return_macro,
)
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.guarded_parity_binding import (
    JoinedParityComposition,
)
from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin
from number_compiler.sequences.collatz.guarded_radix6_bridge import (
    certify_guarded_radix6_bridge,
)
from number_compiler.sequences.collatz.joint_harmonic_band import (
    TWO_ODD_HARMONIC_BAND,
)
from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape
from number_compiler.sequences.collatz.source_closed_port_action import (
    MacroTraceGrammar,
    SourceClosedPortAction,
    SourceCongruence,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def _pointed_join(source_value: int, bits: tuple[int, ...]) -> GuardedPortJoin:
    action = DyadicTerminalFieldAction.identity()
    for bit in bits:
        action = action.then(
            DyadicTerminalFieldAction.one_run(1)
            if bit
            else DyadicTerminalFieldAction.zero_run(1)
        )
    source = CollatzTwoSidedCylinder(source_value, source_value, 0, 1)
    guard = SourceCongruence(action.source_residue, action.source_modulus, source.first)
    port = SourceClosedPortAction(
        action, guard, sum(bits), None, MacroTraceGrammar.leaf(())
    )
    bridge = certify_guarded_radix6_bridge(source, action, sum(bits))
    return GuardedPortJoin(
        source,
        port,
        bridge,
        factor_grammar=tuple(((bit,), 1) for bit in bits),
    )


@pytest.mark.parametrize(
    "motif",
    (
        (0, 1, 0, 2, 1),
        (0, 1, 0, 2, 1, 0),
        (1, 0, 2, 1, 0, 1, 0),
        (1, 0, 2, 1, 0, 1, 0, 2),
    ),
)
def test_period_five_through_eight_6305_actions_keep_source_guards(
    motif: tuple[int, ...],
) -> None:
    residue, modulus = PeriodicTail6305Ring.guard_residue(motif, 3)
    adjustment = ((3 - residue) * pow(modulus, -1, 5)) % 5
    source = residue + adjustment * modulus + 5 * modulus * (1 << 30)
    ring = PeriodicTail6305Ring.from_source(source, motif)

    assert ring.admits(3)
    assert ring.endpoint(3) == collatz_literal(source, 3 * ring.physical_ticks)
    macro = select_border_return_macro(source, 1000)
    assert macro is not None
    assert macro.zero_tails[: len(motif) * 3] == motif * 3
    assert macro.endpoint == collatz_literal(source, macro.physical_ticks)


@pytest.mark.parametrize(
    ("source", "ticks", "check_ports"),
    (
        ((1 << 70) - 1, 101, False),
        (3 * (1 << 32) - 1, 65, True),
        ((1 << 18) - 1, 37, True),
    ),
)
def test_scalar_band_checks_partial_and_base_six_inlets_before_d8(
    source: int, ticks: int, check_ports: bool
) -> None:
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(source, ticks, ledger=ledger)

    assert result.endpoint == collatz_literal(source, ticks)
    assert (
        ledger.counters.get(
            metric_keys.COLLATZ_PHYSICAL_TEMPORAL_JOINT_HARMONIC_BAND_PUMPS, 0
        )
        >= 1
    )
    if check_ports:
        assert (
            ledger.counters.get(
                metric_keys.COLLATZ_PHYSICAL_TEMPORAL_JOINT_XOR_FIVE_PORT_CHECKS, 0
            )
            >= 1
        )
    assert (
        ledger.counters.get(
            metric_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_DISCOVERY_REQUESTS, 0
        )
        == 0
    )


def test_source_free_band_identity_and_joint_period_are_explicit() -> None:
    first = TWO_ODD_HARMONIC_BAND.point(63)
    second = TWO_ODD_HARMONIC_BAND.point((1 << 20) - 1)

    assert first.semantic_key == second.semantic_key
    assert first.semantic_key == TWO_ODD_HARMONIC_BAND.semantic_key
    assert first.joint_cyclotomic_period(2) == 15
    assert second.v5_return_defect(5) == 2
    assert second.base6_five_band_after_odd_steps(10) == 10


def _adjacent_bound_ports() -> tuple[GuardedPortJoin, GuardedPortJoin]:
    first = _pointed_join(13, (1, 0))
    second = _pointed_join(first.port.endpoint(13), (0, 1))
    first_tape = first.parity_tape_for_action()
    second_tape = second.parity_tape_for_action()
    assert first_tape is not None and second_tape is not None
    return first, second


def test_joined_parity_tape_uses_parent_actions_without_historical_refold(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    first, second = _adjacent_bound_ports()
    original_action = ParityCarryTape.action

    def forbidden_action(
        _tape: ParityCarryTape,
    ) -> DyadicTerminalFieldAction:
        raise AssertionError("join refolded the complete historical parity tape")

    monkeypatch.setattr(ParityCarryTape, "action", forbidden_action)
    joined = first.then(second)
    assert joined is not None and joined.parity_tape is not None
    monkeypatch.setattr(ParityCarryTape, "action", original_action)
    assert joined.parity_tape.action().coefficient_snapshot() == (
        joined.port.action.coefficient_snapshot()
    )
    assert joined.parity_tape.prefix_letters(4) == (1, 0, 0, 1)


def test_joined_parity_token_binds_order_for_equal_weight_words() -> None:
    first, second = _adjacent_bound_ports()
    joined = first.then(second)
    assert joined is not None and joined.parity_tape is not None

    alternate = ParityCarryTape.sequence(
        (
            ParityCarryTape.letters((0, 1)),
            ParityCarryTape.letters((1, 0)),
        )
    )
    assert alternate.steps == joined.parity_tape.steps
    assert alternate.odds == joined.parity_tape.odds
    assert alternate.prefix_letters(4) == (0, 1, 1, 0)
    assert joined.parity_tape.prefix_letters(4) == (1, 0, 0, 1)
    assert joined.parity_tape != alternate
    assert alternate.action().coefficient_snapshot() != (
        joined.port.action.coefficient_snapshot()
    )
    with pytest.raises(ValueError, match="parity binding action does not match"):
        replace(joined, parity_tape=alternate)

    class ForeignComposition(JoinedParityComposition):
        def verify(
            self, root: ParityCarryTape, action: DyadicTerminalFieldAction
        ) -> None:
            raise AssertionError("foreign proof verifier must never be dispatched")

    foreign = object.__new__(ForeignComposition)
    with pytest.raises(ValueError, match="exact proof token"):
        replace(joined, _composed_parity=foreign)


def test_join_rejects_equal_weight_parent_tape_replacement() -> None:
    first, second = _adjacent_bound_ports()
    original = first.parity_tape_for_action()
    assert original is not None
    alternate = ParityCarryTape.letters((0, 1))
    assert alternate.steps == original.steps
    assert alternate.odds == original.odds
    assert alternate.action().coefficient_snapshot() != (
        first.port.action.coefficient_snapshot()
    )

    # Simulate stale/foreign object reuse that bypasses dataclass immutability.
    object.__setattr__(first, "parity_tape", alternate)
    with pytest.raises(ValueError, match="parity tape no longer matches"):
        first.then(second)


def test_budgeted_guarded_join_stays_fail_closed_before_composition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    first = _pointed_join(63, (1, 1))
    second = _pointed_join(first.port.endpoint(63), (1,))

    def forbidden_compose(
        _first: SourceClosedPortAction, _after: SourceClosedPortAction
    ) -> SourceClosedPortAction:
        raise AssertionError("source composition started before budget refusal")

    monkeypatch.setattr(SourceClosedPortAction, "then", forbidden_compose)
    ledger = ResourceLedger()
    with pytest.raises(BlockContextBudgetExceeded, match="complete ledger-owned"):
        first.then(second, ledger=ledger)
    assert (ledger.entries, ledger.nodes, ledger.peak_entries, ledger.peak_nodes) == (
        0,
        0,
        0,
        0,
    )
