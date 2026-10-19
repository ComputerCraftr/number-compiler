"""Future-closed, source-certified 6305 carry-cone Moore/power checks."""

from __future__ import annotations

from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_harmonic_ring import PeriodicTail6305Ring
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.conditional_border_moore import (
    ConditionalBorderBudgetExceeded,
    ConditionalPoweredBranch,
    compile_conditional_border_moore,
    compile_conditional_return_power,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    SourceClosedPortAction,
    SourceCongruence,
)
from number_compiler.sequences.collatz.temporal_source_morphism import (
    PointedCollatzSource,
    certified_collatz_root_from_port,
)


def _v2(x: int) -> int:
    return (x & -x).bit_length() - 1


def _one_return(source: int) -> tuple[int, int, int]:
    assert source % 10 == 3
    j = _v2(3 * source + 1) - 1
    # Border action has two odd normalized steps and j zero steps.
    action = (
        DyadicTerminalFieldAction.one_run(1)
        .then(DyadicTerminalFieldAction.zero_run(j))
        .then(DyadicTerminalFieldAction.one_run(1))
    )
    return j, action.endpoint(source), j + 4


def _sample_n(motif: tuple[int, ...], copies: int) -> int:
    r, m = PeriodicTail6305Ring.guard_residue(motif, copies)
    r += (((3 - r) * pow(m, -1, 5)) % 5) * m
    return r + 5 * m * (1 << 512)


def _assert_two_return_matches(
    branch: ConditionalPoweredBranch,
    source: int,
    endpoint: int,
    physical_ticks: int,
    tails: tuple[int, int],
) -> None:
    assert branch.port is not None
    assert branch.port.endpoint(source) == endpoint
    assert branch.physical_ticks == physical_ticks
    assert branch.tails.materialize() == tails


def test_two_source_collision_is_split_as_conditional_actions() -> None:
    family = CollatzTwoSidedCylinder(73, 153, 73, 80)
    assert family.forced_border_word_for_ticks(9) is None
    nine = compile_conditional_border_moore(family, 9, max_tail=6)
    eleven = compile_conditional_border_moore(family, 11, max_tail=6)
    a = nine.select(73)
    b = eleven.select(153)
    assert a is not None and a.tails == (1, 0)
    assert b is not None and b.tails == (1, 2)
    assert a.action.endpoint(73) == 188
    assert b.action.endpoint(153) == 98
    assert a.action.admits(73) and not a.action.admits(153)
    assert b.action.admits(153) and not b.action.admits(73)
    assert nine.select(153) is None and eleven.select(73) is None
    assert nine.class_count <= len(nine.states)
    assert nine.observation()["all_inlet_partitions_conserved"] is True


def test_conditional_next_tail_and_exit_edges_are_disjoint_and_complete() -> None:
    for limit in (2, 4, 6, 8):
        group = CollatzTwoSidedCylinder(3, 3003, 3, 10)
        graph = compile_conditional_border_moore(
            group, 12, max_tail=limit, max_states=600
        )
        for state in graph.states:
            if state.status == "active":
                assert sum(e.inlet.count for e in state.edges) == state.cylinder.count
                for x in (state.cylinder.first, state.cylinder.last):
                    assert sum(e.inlet.contains(x) for e in state.edges) == 1
                for edge in state.edges:
                    if edge.action is not None:
                        assert edge.target is not None
                        assert edge.successor is not None
                        assert edge.endpoint_border in (3, 4, 8, 9)
                        for source in (edge.inlet.first, edge.inlet.last):
                            assert edge.action.certifies(source)
                            endpoint = edge.action.endpoint(source)
                            assert edge.target.contains(endpoint)
                            assert endpoint % 10 == edge.endpoint_border


def test_eight_border_exits_to_four_or_nine_remain_guarded_actions() -> None:
    for source, ticks, expected in ((13, 7, 4), (43, 5, 49), (153, 12, 49)):
        cylinder = CollatzTwoSidedCylinder(source, source, 0, 1)
        ring = compile_conditional_border_moore(
            cylinder, ticks, max_tail=12, max_states=100
        )
        chosen = ring.select(source)
        assert chosen is not None
        assert chosen.action.endpoint(source) == expected
        assert chosen.action.odd_events == 2 * len(chosen.tails)
        assert chosen.action.action.steps + chosen.action.odd_events == ticks
        assert expected % 10 in (4, 9)
    # A 9->9 cycle can also be composed with the preceding 6305 return.
    for ticks, result, odd in ((8, 29, 3), (10, 44, 4)):
        nine = compile_conditional_border_moore(
            CollatzTwoSidedCylinder(33, 33, 0, 1), ticks, max_tail=12
        )
        selected = nine.select(33)
        assert selected is not None
        assert selected.tails == (1,)
        assert selected.action.endpoint(33) == result
        assert selected.action.odd_events == odd
        assert selected.skew_clock.odds == odd
        assert selected.skew_clock.physical_ticks == ticks
        assert selected.action.action.steps + odd == ticks
    # One physical tick cannot contain half of a normalized odd step.
    nine_partial = compile_conditional_border_moore(
        CollatzTwoSidedCylinder(33, 33, 0, 1), 9, max_tail=12
    )
    assert nine_partial.select(33) is None


def test_unresolved_long_tail_and_partial_tick_remain_refusals() -> None:
    group = CollatzTwoSidedCylinder(3, 503, 3, 10)
    graph = compile_conditional_border_moore(group, 4, max_tail=2)
    assert any(edge.refusal == "unresolved_long_tail" for edge in graph.states[0].edges)
    assert any(
        edge.refusal == "partial_physical_return" for edge in graph.states[0].edges
    )
    assert graph.select(53) is None  # zero tail 4 cannot be guessed as 0 or 1
    assert graph.select(33) is None  # zero tail 1 costs five physical ticks


def test_two_return_conditional_temporal_square_preserves_both_tails() -> None:
    family = CollatzTwoSidedCylinder(73, 153, 73, 80)
    one = compile_conditional_return_power(family, 0, max_tail=8)
    two = compile_conditional_return_power(family, 1, max_tail=8)
    assert len(one.branches) == 1 and one.branches[0].tails.length == 1
    assert len(two.branches) == 2
    assert sum(b.inlet.count for b in two.branches) == 2
    assert two.select(73).tails.materialize() == (1, 0)
    assert two.select(153).tails.materialize() == (1, 2)
    for x in (73, 153):
        b = two.select(x)
        assert b.port is not None and b.target is not None
        first_tail, y, first_ticks = _one_return(x)
        second_tail, z, second_ticks = _one_return(y)
        _assert_two_return_matches(
            b, x, z, first_ticks + second_ticks, (first_tail, second_tail)
        )
    assert two.class_count == 2


def test_long_certified_motif_squares_without_expanding_return_trace() -> None:
    x = _sample_n((0, 1), copies=8)
    source = CollatzTwoSidedCylinder.from_pointed_source(
        x, binary_bits=300, leading_bits=8
    )
    powered = compile_conditional_return_power(source, 4, max_tail=8)
    selected = powered.select(x)
    assert selected.port is not None and selected.refusal is None
    assert len(powered.branches) == 1
    assert selected.tails.length == 16
    assert selected.tails.materialize() == (0, 1) * 8
    assert selected.physical_ticks == 8 * 9
    assert selected.port.odd_events == 32
    actual = x
    for tail in (0, 1) * 8:
        j, actual, _ = _one_return(actual)
        assert j == tail
    assert selected.port.endpoint(x) == actual
    assert selected.target is not None and selected.target.contains(actual)
    clock = powered.demanded_pointed_clock(x)
    assert clock is not None
    assert (clock.odds, clock.steps, clock.physical_ticks) == (
        selected.port.odd_events,
        selected.port.action.steps,
        selected.physical_ticks,
    )


def test_pure_6305_hundred_return_word_uses_compressed_binary_power() -> None:
    # The centered coefficient 2 modulo 5 forces a 3-ending source.
    x = (1 << 257) * (2 + 5 * (1 << 512)) - 1
    assert x % 10 == 3
    source = CollatzTwoSidedCylinder.from_pointed_source(
        x, binary_bits=300, leading_bits=8
    )
    power = compile_conditional_return_power(source, 7, max_tail=5)
    assert len(power.branches) == 1
    block = power.select(x)
    assert block.port is not None and block.tails.length == 128
    assert block.physical_ticks == 512
    assert block.port.action.steps == 256
    assert block.port.endpoint(x) == 9**128 * ((x + 1) >> 256) - 1
    with pytest.raises(BlockContextBudgetExceeded):
        block.tails.materialize(max_labels=20)


def test_scalar_reference_through_4096_small_three_border_sources() -> None:
    for x in range(3, 4096, 10):
        group = CollatzTwoSidedCylinder(x, x, 0, 1)
        two = compile_conditional_return_power(group, 1, max_tail=9)
        selected = two.select(x)
        j, y, t1 = _one_return(x)
        if j >= 9 or y % 10 != 3:
            assert selected.port is None
            continue
        k, z, t2 = _one_return(y)
        if k >= 9:
            assert selected.port is None
            continue
        assert selected.port is not None
        assert selected.port.admits(x)
        _assert_two_return_matches(selected, x, z, t1 + t2, (j, k))


def test_root_true_endpoint_conditional_path_replaces_eager_compile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    motif = (0, 2, 1, 1)
    x = _sample_n(motif, copies=1)
    action = DyadicTerminalFieldAction.identity()
    for j in motif[:2]:
        one = DyadicTerminalFieldAction.one_run(1)
        action = action.then(one.then(DyadicTerminalFieldAction.zero_run(j)).then(one))
    guard = SourceCongruence(action.source_residue, action.source_modulus).meet(
        SourceCongruence(3, 5)
    )
    assert guard is not None
    port = SourceClosedPortAction(action, guard, 4, None)
    ticks = sum(j + 4 for j in motif[:2])
    owner = PointedCollatzSource.issue(x, 2 * ticks, ledger=ResourceLedger())
    first = certified_collatz_root_from_port(owner, port)

    import number_compiler.sequences.collatz.collatz_two_sided_ring as cylinders
    import number_compiler.sequences.collatz.temporal_run_quotient as original

    # Force the old common-to-entire-fiber exit to exercise the conditional graph.
    monkeypatch.setattr(
        cylinders.CollatzTwoSidedCylinder,
        "forced_border_word_for_ticks",
        lambda *_a, **_kw: None,
    )
    monkeypatch.setattr(
        original,
        "compile_collatz_temporal_run_quotient",
        lambda *_a, **_kw: (_ for _ in ()).throw(
            AssertionError("eager D8 was invoked")
        ),
    )
    powered = first.square()
    assert powered.port_action is not None
    assert powered.last.value == _one_return(_one_return(first.last.value)[1])[1]
    assert powered.port_action.endpoint(x) == powered.last.value
    assert powered.radial_clock.scale.growths == 8


def test_joint_requested_prime_walsh_and_width_ports_use_same_selected_guard() -> None:
    group = CollatzTwoSidedCylinder(73, 153, 73, 80)
    graph = compile_conditional_border_moore(group, 9, max_tail=6)
    port = graph.demanded_pointed_ports(
        73,
        binary_bits=24,
        radix_places={3: 2, 6: 2, 10: 2, 64: 64},
        walsh64=True,
        include_width_coverage=True,
    )
    tails = cast(tuple[int, ...], port["conditional_proved_tails"])
    radial_scale = cast(tuple[int, int], port["radial_scale"])
    requested_ports = cast(dict[str, object], port["demanded_radix_walsh_ports"])
    clock = cast(tuple[int, int, int], port["quadratic_clock"])
    root_guard = cast(tuple[int, int], port["conditional_root_source_guard"])
    assert tails == (1, 0)
    assert radial_scale == (4, 5)
    assert requested_ports["endpoint"] == 188
    assert "radix6_digit_coverage" in port
    assert port["all_alternatives_retained"] is True
    assert port["source_bound_skew_verified"] is True
    assert len(clock) == 3
    residue, modulus = root_guard
    assert 73 % modulus == residue
    assert 153 % modulus != residue
    with pytest.raises(ValueError, match="unresolved conditional inlet"):
        graph.demanded_pointed_ports(153)


def test_demanded_conditional_graph_and_return_power_from_true_root() -> None:
    owner = PointedCollatzSource.issue(23, 24, ledger=ResourceLedger())
    action = DyadicTerminalFieldAction.one_run(2)
    port = SourceClosedPortAction(action, SourceCongruence(3, 20), 2, None)
    pointed = certified_collatz_root_from_port(owner, port)
    assert pointed.last.value == 53
    packet = pointed.demanded_conditional_border_moore(
        8, binary_bits=8, leading_bits=3, max_tail=8
    )
    assert packet["pointed_tails"] == (4,)
    assert packet["pointed_endpoint"] == 8
    assert packet["source_issued"] is True
    power = pointed.demanded_conditional_return_power(
        1, binary_bits=8, leading_bits=3, max_tail=8
    )
    assert power["pointed_refusal"] == "exit_before_requested_return_count"
    assert power["pointed_endpoint"] is None
    assert power["globally_closed"] is False


def test_budgets_are_guarded_and_source_must_be_authorized() -> None:
    group = CollatzTwoSidedCylinder(3, 20003, 3, 10)
    with pytest.raises(ConditionalBorderBudgetExceeded):
        compile_conditional_border_moore(group, 64, max_tail=10, max_states=2)
    with pytest.raises(ValueError):
        compile_conditional_border_moore(group, 0)
    with pytest.raises(ValueError):
        compile_conditional_return_power(group, 13)
    with pytest.raises(ValueError):
        compile_conditional_return_power(group, 2, max_tail=0)
    graph = compile_conditional_border_moore(group, 4, max_tail=4, max_states=100)
    with pytest.raises(ValueError):
        graph.select(17)
