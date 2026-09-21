"""Compressed carry observation; literal words occur only in bounded oracles."""

from itertools import pairwise

import pytest

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.carry.event_memory import (
    forcing_difference_alphabet,
    forcing_event,
    forcing_event_alphabet,
    pair_step,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.live_carry_projection import (
    project_centered_residue_carries,
    project_live_pair_carries,
    recover_centered_carry_events,
)
from number_compiler.arithmetic.fields.live_forcing import LiveForcingProjection
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.arithmetic.fields.test_centered_carry import _evaluate, _polynomial


@pytest.mark.parametrize("incoming", [0, 1])
def test_direct_events_match_literal_carry_for_every_pair_symbol(incoming: int) -> None:
    # Includes wires, unchanged resets, changes at seams and asymmetric fields.
    for pair in ([p] * 3 + [9, 9, 18 - p, 0, 18] for p in range(19)):
        ledger = ResourceLedger()
        arena = SymbolicInnovationArena(ledger)
        residual = _polynomial(arena, [p - 9 for p in pair])
        events = recover_centered_carry_events(
            arena, residual, extent=len(pair), incoming=incoming
        )
        carry = incoming
        resets: dict[int, int] = {}
        correction: dict[int, int] = {}
        for i, p in enumerate(pair):
            after = int(p + carry >= 10)
            resets[i] = after - carry
            correction[i] = correction.get(i, 0) - 10 * after
            correction[i + 1] = after
            carry = after
        assert events.terminal_carry == carry
        assert _evaluate(arena, events.reset_jumps) == {
            i: x for i, x in resets.items() if x
        }
        assert _evaluate(arena, events.correction) == {
            i: x for i, x in correction.items() if x
        }
        arena.close()
        assert ledger.entries == ledger.nodes == 0


def test_direct_events_merge_carry_domains_without_spatial_expansion(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("carry event recovery constructed a word grammar")

    monkeypatch.setattr(SLPArena, "__init__", forbidden)
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    width = 1 << 200
    # P = 18, then an enormous 9-wire, then 10, then 0. All first three
    # quotient intervals share a single carry-one domain despite different P.
    residual = arena.linear_combination(
        (
            (9, arena.interval(1)),
            (1, arena.chart(arena.interval(1), CylinderChart(1, -width))),
            (-9, arena.chart(arena.interval(1), CylinderChart(1, -width - 1))),
        )
    )
    before = arena.node_count
    events = recover_centered_carry_events(arena, residual, extent=width + 2)
    assert events.terminal_carry == 0
    assert ledger.counters["carry_event_domain_actions"] == 4
    assert ledger.counters["carry_event_reset_events"] == 2
    assert ledger.counters["carry_event_occupied_intervals"] == 1
    assert arena.node_count - before < 25
    with LiveForcingProjection(arena, events.reset_jumps) as view:
        assert tuple(
            (r.start, r.stop, r.residue) for r in view.residue_runs(0, width + 2)
        ) == ((0, 1, 1), (1, width + 1, 0), (width + 1, width + 2, 31))
    arena.close()
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("incoming", [0, 1])
def test_direct_neutral_domain_preserves_incoming_without_reset(incoming: int) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    events = recover_centered_carry_events(
        arena, arena.zero, extent=7, incoming=incoming
    )
    assert events.terminal_carry == incoming
    assert events.reset_jumps == arena.zero
    correction = _evaluate(arena, events.correction)
    assert correction == (
        {0: -10, **dict.fromkeys(range(1, 7), -9), 7: 1} if incoming else {}
    )
    arena.close()


def test_direct_recovery_rejects_foreign_and_invalid_residuals() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    foreign = SymbolicInnovationArena(ResourceLedger())
    retained = ledger.entries, ledger.nodes
    with pytest.raises(ValueError, match="different arena"):
        recover_centered_carry_events(arena, foreign.zero, extent=3)
    assert (ledger.entries, ledger.nodes) == retained
    residual = arena.linear_combination(((22, arena.interval(1)),))  # P=31
    with pytest.raises(ValueError, match="pair range"):
        recover_centered_carry_events(arena, residual, extent=1)
    assert ledger.counters.get("carry_event_domain_actions", 0) == 0
    foreign.close()
    arena.close()
    assert ledger.entries == ledger.nodes == 0


def test_direct_recovery_cancels_before_sign_and_retains_terminal_seam() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    positive = arena.linear_combination(((9, arena.interval(3)),))
    negative = arena.linear_combination(((-9, arena.interval(3)),))
    # The cancelling packets must not emit a spurious carry reset. The only
    # non-neutral site is the middle one: P=(9,18,9), with growth at the end.
    residual = arena.linear_combination(
        (
            (1, positive),
            (1, negative),
            (9, arena.chart(arena.interval(1), CylinderChart(1, -1))),
        )
    )
    events = recover_centered_carry_events(arena, residual, extent=3)
    assert _evaluate(arena, events.reset_jumps) == {1: 1}
    assert events.terminal_carry == 1
    assert _evaluate(arena, events.correction) == {1: -10, 2: -9, 3: 1}
    assert ledger.counters["carry_event_reset_events"] == 1
    arena.close()


def test_direct_events_do_not_grant_source_authority_from_residue_range() -> None:
    from number_compiler.sequences.reverse_add.source_images import (
        ReverseSourceImageWorkspace,
    )

    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    workspace = ReverseSourceImageWorkspace(ledger, 196, 0)
    # Formal P=32 aliases to zero, so the arithmetic observer's result is
    # conditional and must never be accepted as an admitted successor image.
    residual = arena.linear_combination(((23, arena.interval(1)),))
    events = recover_centered_carry_events(arena, residual, extent=1)
    assert events.terminal_carry == 0
    with pytest.raises(TypeError, match="payload sort"):
        workspace.adapter.validate_payload(events)
    workspace.dispose()
    arena.close()
    assert ledger.entries == ledger.nodes == 0


def test_residue_lease_refuses_before_allocating_result(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    with LiveForcingProjection(arena, arena.interval(1 << 200)) as view:
        held = ledger.nodes, ledger.entries
        ledger.max_nodes = ledger.nodes

        def forbidden(*_args: object, **_kwargs: object) -> tuple[()]:
            raise AssertionError("residue result allocated before lease admission")

        monkeypatch.setattr(LiveForcingProjection, "residue_runs", forbidden)
        with (
            pytest.raises(BlockContextBudgetExceeded),
            view.leased_residue_runs(0, 1 << 200),
        ):
            pytest.fail("refused lease was published")
        assert (ledger.nodes, ledger.entries) == held
    arena.close()
    assert ledger.entries == ledger.nodes == 0


def test_residue_lease_releases_after_consumer_failure() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    with LiveForcingProjection(arena, arena.interval(100)) as view:
        held = ledger.nodes, ledger.entries
        with (
            pytest.raises(RuntimeError, match="consumer"),
            view.leased_residue_runs(0, 100) as runs,
        ):
            assert (ledger.nodes, ledger.entries) != held
            assert len(runs) == 1
            raise RuntimeError("consumer failed")
        assert (ledger.nodes, ledger.entries) == held
    arena.close()
    assert ledger.entries == ledger.nodes == 0


def test_forcing_alphabet_is_beta_not_its_difference() -> None:
    # Seed 196 has pair P=(7,18,7). This is an exact admitted original source.
    source = (7, 18, 7)
    target, growth = pair_step(source, 10)
    beta = forcing_event(source, target, growth)
    assert beta == (1, -20, 1)
    derivative = (beta[0], beta[1] - beta[0], beta[2] - beta[1], -beta[-1])
    assert derivative == (1, -21, 21, -1)
    assert set(beta) <= set(forcing_event_alphabet(10))
    assert not set(derivative) <= set(forcing_event_alphabet(10))
    assert set(derivative) <= set(forcing_difference_alphabet(10))


def test_differentiated_growth_forcing_keeps_terminal_seam() -> None:
    source = (18, 0, 18)  # seed 909
    target, growth = pair_step(source, 10)
    beta = forcing_event(source, target, growth)
    assert growth == 1 and beta == (-9, -9, -9, -9)
    derivative = (beta[0], *(b - a for a, b in pairwise(beta)), -beta[-1])
    assert derivative == (-9, 0, 0, 0, 9)
    assert 9 not in forcing_event_alphabet(10)
    assert set(derivative) <= set(forcing_difference_alphabet(10))


@pytest.mark.parametrize("seed", [0, 1, 18, 196, 909, 1041, 1051, 1593])
@pytest.mark.parametrize("incoming", [0, 1])
def test_pair_residues_flow_through_shared_carry_grammar(
    seed: int, incoming: int
) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    digits = tuple(map(int, str(seed)[::-1]))
    pair = [a + b for a, b in zip(digits, reversed(digits), strict=True)]
    expression = _polynomial(arena, pair)
    retained = ledger.entries, ledger.nodes
    carry = incoming
    expected_carry: list[int] = []
    expected_jumps: list[int] = []
    for p in pair:
        next_carry = int(p + carry >= 10)
        expected_carry.append(next_carry)
        expected_jumps.append(next_carry - carry)
        carry = next_carry
    with (
        LiveForcingProjection(arena, expression) as view,
        project_live_pair_carries(
            view, start=0, stop=len(pair), incoming=incoming
        ) as result,
    ):
        assert result.arena.materialize(result.outgoing_root) == tuple(expected_carry)
        assert result.arena.materialize(result.jump_root) == tuple(expected_jumps)
        assert result.final_carry == carry
    assert (ledger.entries, ledger.nodes) == retained


def test_huge_neutral_run_does_not_materialize(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    width = 1 << 200
    expression = arena.linear_combination(((9, arena.interval(width)),))

    def forbidden(_self: SLPArena, _root: int) -> tuple[int, ...]:
        raise AssertionError("represented word was materialized")

    monkeypatch.setattr(SLPArena, "materialize", forbidden)
    retained = ledger.entries, ledger.nodes
    with (
        LiveForcingProjection(arena, expression) as view,
        project_live_pair_carries(view, start=0, stop=width, incoming=1) as result,
    ):
        assert result.input_length == width
        assert result.final_carry == 1
        assert result.derived_nodes < 10000
    assert ledger.counters["live_carry_input_runs"] == 1
    assert (ledger.entries, ledger.nodes) == retained


def test_invalid_modular_pair_and_precision_fail_without_retention() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    expression = arena.linear_combination(((31, arena.interval(2)),))
    retained = ledger.entries, ledger.nodes
    with LiveForcingProjection(arena, expression) as view:
        held = ledger.entries, ledger.nodes
        with pytest.raises(ValueError, match="pair range"):
            project_live_pair_carries(view, start=0, stop=2)
        assert (ledger.entries, ledger.nodes) == held
    assert (ledger.entries, ledger.nodes) == retained
    with (
        LiveForcingProjection(arena, arena.interval(1), bits=4) as view,
        pytest.raises(ValueError, match="modulo 32"),
    ):
        project_live_pair_carries(view, start=0, stop=1)


def test_translated_view_keeps_physical_order() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    pair = _polynomial(arena, [18, 9, 0])
    translated = arena.chart(pair, CylinderChart(1, 10))
    with (
        LiveForcingProjection(arena, translated) as view,
        project_live_pair_carries(view, start=-10, stop=-7) as result,
    ):
        assert result.arena.materialize(result.outgoing_root) == (1, 1, 0)
        assert result.arena.materialize(result.jump_root) == (1, 0, -1)


def test_recovered_modular_carry_is_not_source_admission() -> None:
    from number_compiler.sequences.reverse_add.source_images import (
        ReverseSourceImageWorkspace,
    )

    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    workspace = ReverseSourceImageWorkspace(ledger, 196, 0)
    # 39 aliases to 7 modulo32. Numeric range alone must not grant admission.
    expression = arena.linear_combination(((39, arena.interval(1)),))
    with (
        LiveForcingProjection(arena, expression) as view,
        project_live_pair_carries(view, start=0, stop=1) as result,
        pytest.raises(TypeError, match="payload sort"),
    ):
        workspace.adapter.validate_payload(result)
    workspace.dispose()
    arena.close()
    assert ledger.entries == ledger.nodes == 0


def test_centered_clock_uncenters_before_sign_recovery() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    residual = _polynomial(arena, [-2, 9, -2])  # Delta for original 196
    with project_centered_residue_carries(arena, residual, extent=3) as result:
        assert result.arena.materialize(result.outgoing_root) == (0, 1, 0)
        assert result.arena.materialize(result.closed_jump_root) == (0, 1, -1, 0)
    arena.close()
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("seed", [1, 196])
def test_bounded_orbit_crosses_growth_and_neutral_runs(seed: int) -> None:
    value = seed
    for _ in range(32):
        digits = tuple(map(int, str(value)[::-1]))
        pair = [a + b for a, b in zip(digits, reversed(digits), strict=True)]
        carry = 0
        expected: list[int] = []
        for p in pair:
            carry = int(p + carry >= 10)
            expected.append(carry)
        ledger = ResourceLedger()
        arena = SymbolicInnovationArena(ledger)
        residual = _polynomial(arena, [p - 9 for p in pair])
        with project_centered_residue_carries(
            arena, residual, extent=len(pair)
        ) as result:
            assert result.arena.materialize(result.outgoing_root) == tuple(expected)
            assert result.final_carry == carry
        arena.close()
        assert ledger.entries == ledger.nodes == 0
        value += int(str(value)[::-1])


def test_seven_symbol_witness_uses_authenticated_primitive_owner() -> None:
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.sequences.reverse_add.cylinder_innovation import (
        primitive_successor_clause,
    )
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    ports = SourceCarryPorts(ExactSource((6, 9, 1), 10, orbit="reverse-add"), ledger)
    clause = primitive_successor_clause(arena, ports)
    beta = tuple(clause.beta_coefficient(i) for i in range(clause.output_extent))
    assert beta == (1, -20, 1)
    assert (beta[0], *(b - a for a, b in pairwise(beta)), -beta[-1]) == (
        1,
        -21,
        21,
        -1,
    )
    # A symbolic beta binding is not permission to evaluate an unresolved
    # future/source atom through the modular interval-only consumer.
    with (
        LiveForcingProjection(arena, clause.beta) as view,
        pytest.raises(TypeError, match="unresolved atom"),
    ):
        project_live_pair_carries(view, start=0, stop=clause.output_extent)
    clause.close()
    ports.dispose()
    arena.close()
    assert ledger.entries == ledger.nodes == 0
