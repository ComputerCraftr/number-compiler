"""Adversarial tests for source-punctured radix-6 and decimal carry ports."""

from __future__ import annotations

from unittest.mock import patch

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
    mul3_two_digit_carries,
)
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.cross_family_port_power import (
    CrossFamilyPortAction,
    MacroTraceGrammar,
    SourceCongruence,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.guarded_port_join import (
    GuardedPortJoin,
    PortPuncture,
)
from number_compiler.sequences.collatz.guarded_radix6_bridge import (
    certify_guarded_radix6_bridge,
)


def _join(
    source: CollatzTwoSidedCylinder,
    action: DyadicTerminalFieldAction,
    odds: int,
    tails: tuple[int, ...] = (),
) -> GuardedPortJoin:
    guard = (
        SourceCongruence(action.source_residue, action.source_modulus, source.first)
        if source.count == 1
        else SourceCongruence(source.residue, source.modulus, source.first)
    )
    port = CrossFamilyPortAction(
        action, guard, odds, None, MacroTraceGrammar.leaf(tails)
    )
    bridge = certify_guarded_radix6_bridge(source, action, odds)
    return GuardedPortJoin(source, port, bridge)


def _pointed_zero_tail_join(
    returns: int, *, source_slack: int = 0
) -> tuple[int, DyadicTerminalFieldAction, GuardedPortJoin]:
    steps = 2 * returns
    source_value = (1 << (steps + source_slack)) - 1
    source = CollatzTwoSidedCylinder(source_value, source_value, 0, 1)
    action = DyadicTerminalFieldAction.one_run(2).power(returns)
    return source_value, action, _join(source, action, steps, (0,) * returns)


def test_63_263_split_only_at_the_requested_upper_parity_cut() -> None:
    source = CollatzTwoSidedCylinder(63, 263, 63, 200)
    joined = _join(source, DyadicTerminalFieldAction.one_run(2), 2)

    first = joined.puncture(0)
    assert first.admitted_count == 2
    assert [
        (row.input_pair, row.upper_parity, row.output_pair, row.count)
        for row in first.rows
    ] == [(63, 0, 95, 2)]

    second = joined.puncture(1)
    assert second.prefix_scalar_steps == 1
    assert second.admitted_count == 2
    assert {
        (row.input_pair, row.upper_parity, row.output_pair, row.count)
        for row in second.rows
    } == {(95, 0, 43, 1), (95, 1, 93, 1)}
    for source_value, output in ((63, 43), (263, 93)):
        row = second.pointed(source_value)
        assert row is not None and row.output_pair == output
    assert joined.puncture(1, PortPuncture(output_pair=93)).pointed(63) is None
    assert joined.puncture(1, PortPuncture(output_pair=93)).pointed(263) is not None
    assert joined.puncture(1, PortPuncture(hundreds=1)).admitted_count == 0
    assert joined.puncture(1, PortPuncture(hundreds=2)).admitted_count == 2
    with pytest.raises(BlockContextBudgetExceeded):
        joined.puncture(1, max_rows=1)
    with pytest.raises(ValueError):
        PortPuncture(five_carry=True)


def test_intermediate_prefix_budget_is_checked_before_scalar_decode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = CollatzTwoSidedCylinder(63, 63, 0, 1)
    joined = _join(source, DyadicTerminalFieldAction.one_run(2), 2)

    def forbidden_prefix(
        _joined: GuardedPortJoin, _time: int
    ) -> tuple[DyadicTerminalFieldAction, int]:
        raise AssertionError("out-of-budget prefix was decoded")

    monkeypatch.setattr(GuardedPortJoin, "_prefix", forbidden_prefix)
    with pytest.raises(BlockContextBudgetExceeded, match="prefix exceeds"):
        joined.puncture(1, max_prefix_steps=0)


def test_decimal_puncture_recovers_only_35s_forced_base6_reset() -> None:
    source = CollatzTwoSidedCylinder(35, 39, 3, 4)
    joined = _join(source, DyadicTerminalFieldAction.one_run(1), 1)
    assert joined.bridge.source_fives == ()

    cut = joined.puncture(0, PortPuncture(five_carry=2, five_remainder=1))
    assert cut.admitted_count == 1
    assert cut.pointed(35) is not None
    assert cut.pointed(39) is None
    # Base-6 carry 2 is independent from the decimal hundreds wire (which is 1).
    assert mul3_two_digit_carries(35) == (1, 1)
    assert (
        joined.puncture(0, PortPuncture(five_carry=2, hundreds=2)).admitted_count == 0
    )


def test_upper_word_f5_and_future_border_guards_pull_back_to_source() -> None:
    source = CollatzTwoSidedCylinder(63, 67, 3, 4)
    joined = _join(source, DyadicTerminalFieldAction.one_run(2), 2)

    assert joined.puncture(0, PortPuncture(upper_word=(3, 2, 10))).admitted_count == 1
    assert joined.puncture(0, PortPuncture(upper_word=(3, 2, 11))).admitted_count == 1
    assert joined.puncture(0, PortPuncture(numerator_f5=4)).pointed(63) is not None
    assert joined.puncture(0, PortPuncture(numerator_f5=4)).pointed(67) is None
    future_three = joined.future_border(3)
    assert future_three is not None
    assert future_three.source.first == 63
    future_two = joined.future_border(2)
    assert future_two is not None
    assert future_two.source.first == 67
    assert joined.future_border(7) is None


def test_five_return_power_requires_source_wide_two_and_five_guards(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    returns = 64
    steps = 2 * returns
    source_value, action, joined = _pointed_zero_tail_join(returns, source_slack=2)
    result = joined.authenticate_weighted_ports(source_value, max_steps=8)
    assert result.matrix_power_period == 5
    assert result.port_punctures == 0
    assert (
        result.matrix_compositions,
        result.matrix_squarings,
        result.scalar_steps,
    ) == (
        23,
        3,
        0,
    )

    # Force the exact bounded chronology on the same admitted source. The
    # production fast path reports successful products/squarings from calls;
    # the bounded path reports its actual scalar stages.
    def skip_proved_power(_joined: GuardedPortJoin, _source: int) -> None:
        return None

    monkeypatch.setattr(GuardedPortJoin, "powered_zero_tail_carries", skip_proved_power)
    exact = joined.authenticate_weighted_ports(source_value, max_steps=steps)
    assert (exact.matrix_compositions, exact.matrix_squarings, exact.scalar_steps) == (
        0,
        0,
        steps,
    )
    assert (exact.carry_tens, exact.carry_hundreds, exact.last_pair) == (
        result.carry_tens,
        result.carry_hundreds,
        result.last_pair,
    )

    scalar = source_value
    tens = hundreds = 0
    for _ in range(steps):
        c1, c2 = mul3_two_digit_carries(scalar % 100)
        tens += c1
        hundreds += c2
        scalar = (3 * scalar + 1) // 2
    assert (result.carry_tens, result.carry_hundreds, result.last_pair) == (
        tens,
        hundreds,
        scalar % 100,
    )
    assert scalar == action.endpoint(source_value)

    # A whole source fiber may force every parity but still lack mod 25.
    modulus = 4 << steps
    broad_value = modulus - 1
    broad = CollatzTwoSidedCylinder(
        broad_value, broad_value + modulus, broad_value % modulus, modulus
    )
    broad_join = _join(broad, action, steps, (0,) * returns)
    assert broad.forced_residue(25) is None
    assert broad_join.powered_zero_tail_carries(broad_value) is None
    with pytest.raises(BlockContextBudgetExceeded):
        broad_join.authenticate_weighted_ports(broad_value, max_steps=8)


def test_insufficient_v2_plus_one_never_upgrades_to_powered_inlets() -> None:
    returns = 32
    source_value, _action, joined = _pointed_zero_tail_join(returns)

    assert joined.powered_zero_tail_carries(source_value) is None
    with pytest.raises(BlockContextBudgetExceeded):
        joined.authenticate_weighted_ports(source_value, max_steps=8)


def test_plain_conditional_candidate_keeps_radix6_and_matrix_ports_lazy() -> None:
    import number_compiler.sequences.collatz.guarded_radix6_bridge as bridge_module
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.border_harmonic_ring import (
        PeriodicTail6305Ring,
    )
    from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
        issue_conditional_scheduler_candidate,
    )

    count = 64
    residue, modulus = PeriodicTail6305Ring.guard_residue((0, 1), count)
    residue += ((3 - residue) * pow(modulus, -1, 5) % 5) * modulus
    source = residue + 5 * modulus * (1 << 48)
    ticks = count * 9
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "lazy-matrix-test")

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("plain conditional action constructed radix-6 ports")

    with (
        scratch.scope(),
        patch.object(bridge_module, "certify_return_trace_radix6_bridge", forbidden),
        patch.object(bridge_module, "certify_guarded_radix6_bridge", forbidden),
    ):
        candidate = issue_conditional_scheduler_candidate(
            source, ticks, scratch=scratch, ledger=ledger
        )
    assert candidate is not None
    assert candidate.joined_port is None
    assert candidate.carry_program is None
    assert candidate.upper_sturmian is None
    assert candidate.pair_transfer is None
