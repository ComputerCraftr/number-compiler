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
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.live_carry_projection import (
    project_centered_residue_carries,
    project_live_pair_carries,
)
from number_compiler.arithmetic.fields.live_forcing import LiveForcingProjection
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.arithmetic.fields.test_centered_carry import _polynomial


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
