"""Event arithmetic checks; literal coefficients are bounded test oracles only."""

from __future__ import annotations

from itertools import product

import pytest

from number_compiler.arithmetic.carry.carry_monoid import CarryFn, centered_carry_fn
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.centered_carry import (
    advance_centered_residual,
    carry_coboundary,
    center_pair_field,
    reflected_innovation,
)
from number_compiler.arithmetic.fields.centered_events import (
    advance_centered_events,
    clock_event_tail,
    neutral_carry_jump,
    reset_carry_jump,
)
from number_compiler.arithmetic.fields.event_innovation import (
    event_difference,
    normalize_event_sum,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    RadialMultiplier,
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from tests.arithmetic.fields.test_centered_carry import _evaluate, _polynomial


def test_interval_cancellation_is_exact_without_coefficients() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    for width in (1, 2, 10**200):
        first = arena.interval(width)
        last = arena.chart(arena.interval(1), CylinderChart(1, -width))
        expression = arena.linear_combination(
            ((1, arena.interval(width + 1)), (-1, first), (-1, last))
        )
        assert event_difference(arena, expression) == arena.zero
    assert "symbolic_innovation_projection_visits" not in ledger.counters


@pytest.mark.parametrize(("slope", "offset"), [(1, -4), (1, 3), (-1, -5), (-1, 7)])
def test_event_transport_matches_full_laurent_difference(
    slope: int, offset: int
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    expression = arena.chart(
        arena.radial(arena.interval(5), RadialMultiplier(2, 3)),
        CylinderChart(slope, offset),
    )
    values = _evaluate(arena, expression)
    expected = dict(values)
    for i, value in values.items():
        expected[i + 1] = expected.get(i + 1, 0) - value
    actual = event_difference(arena, expression)
    assert _evaluate(arena, actual) == {i: v for i, v in expected.items() if v}
    assert normalize_event_sum(arena, actual) == actual


def test_enormous_interval_has_only_two_events() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    width = 10**200
    result = event_difference(arena, arena.interval(width))
    assert _evaluate(arena, result) == {0: 1, width: -1}
    assert ledger.counters["event_normalization_contexts"] == 1
    assert ledger.counters["event_normalization_nonzero_terms"] == 2
    report = audit_registered_payloads(ledger)
    assert report.unknown_payloads == report.forbidden_future_payloads == 0
    assert report.unbounded_future_integers == 0


def test_shared_dag_weights_combine_before_child_processing() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    a, b = arena.interval(3), arena.interval(7)
    shared = arena.add(a, b)
    expression = arena.add(arena.add(shared, a), arena.add(shared, b))
    before = arena.node_count
    actual = event_difference(arena, expression)
    assert _evaluate(arena, actual) == {0: 6, 3: -3, 7: -3}
    assert ledger.counters["event_normalization_contexts"] < before
    alternate = arena.linear_combination(((3, a), (3, b)))
    assert event_difference(arena, alternate) == actual


def test_event_tail_restores_leading_value_before_the_next_carry_port() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    # Delta=(2,1) has two positive carry ports, although H=(2,-1,-1).
    events = event_difference(arena, _polynomial(arena, [2, 1]))
    assert _evaluate(arena, events) == {0: 2, 1: -1, 2: -1}
    tail = clock_event_tail(arena, events, extent=2, prefix=0, leading=2)
    assert _evaluate(arena, tail) == {0: 1, 1: -1}
    assert clock_event_tail(arena, tail, extent=1, prefix=0, leading=1) == arena.zero


def test_clock_event_tail_skips_a_huge_zero_prefix_symbolically() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    h = 10**200
    delta = arena.chart(arena.interval(1), CylinderChart(1, -h))
    events = event_difference(arena, delta)
    assert (
        clock_event_tail(arena, events, extent=h + 1, prefix=h, leading=1) == arena.zero
    )


@pytest.mark.parametrize("incoming", [0, 1])
@pytest.mark.parametrize("extent", [0, 1, 10**200])
def test_neutral_jump_retains_only_terminal_boundary(
    incoming: int, extent: int
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    result = neutral_carry_jump(arena, extent=extent, incoming=incoming)
    assert _evaluate(arena, result) == ({extent: -1} if incoming else {})


def test_same_carry_reset_does_not_erase_tail_or_terminal() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    tail = neutral_carry_jump(arena, extent=5, incoming=1)
    result = reset_carry_jump(arena, tail, prefix=7, leading=3, incoming=1)
    assert _evaluate(arena, result) == {13: -1}
    with pytest.raises(ValueError, match="nonzero"):
        reset_carry_jump(arena, tail, prefix=7, leading=0, incoming=1)


def test_same_reset_retains_a_later_opposite_reset() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    # A positive reset with incoming 1 produces no local jump. A later
    # negative reset must still be published, after the prefix translation.
    tail = reset_carry_jump(arena, arena.zero, prefix=4, leading=-2, incoming=1)
    result = reset_carry_jump(arena, tail, prefix=7, leading=3, incoming=1)
    assert _evaluate(arena, result) == {12: -1}
    assert result != arena.zero


def test_event_reset_uses_the_shared_delta_port(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.fields.centered_events as events

    arena = SymbolicInnovationArena(ResourceLedger())
    seen: list[int] = []

    def record(delta: int) -> CarryFn:
        seen.append(delta)
        return centered_carry_fn(delta)

    monkeypatch.setattr(events, "centered_carry_fn", record)
    positive = events.reset_carry_jump(
        arena, arena.zero, prefix=0, leading=9, incoming=0
    )
    negative = events.reset_carry_jump(
        arena, arena.zero, prefix=0, leading=-9, incoming=1
    )
    assert seen == [9, -9]
    assert _evaluate(arena, positive) == {0: 1}
    assert _evaluate(arena, negative) == {0: -1}


def test_jump_recurrence_matches_both_physical_carry_ports() -> None:
    for residual, incoming in product(product((-1, 0, 1), repeat=3), (0, 1)):
        arena = SymbolicInnovationArena(ResourceLedger())
        m = len(residual)
        resets = [i for i, d in enumerate(residual) if d]
        if resets:
            jump = neutral_carry_jump(
                arena,
                extent=m - resets[-1] - 1,
                incoming=int(residual[resets[-1]] > 0),
            )
            for k in reversed(range(len(resets))):
                previous = resets[k - 1] if k else -1
                before = int(residual[previous] > 0) if k else incoming
                jump = reset_carry_jump(
                    arena,
                    jump,
                    prefix=resets[k] - previous - 1,
                    leading=residual[resets[k]],
                    incoming=before,
                )
        else:
            jump = neutral_carry_jump(arena, extent=m, incoming=incoming)
        c = incoming
        q: list[int] = []
        for d in residual:
            c = (d + 9 + c) // 10
            q.append(c)
        expected = {0: -incoming}
        for i, value in enumerate(q):
            expected[i] = expected.get(i, 0) + value
            expected[i + 1] = expected.get(i + 1, 0) - value
        assert _evaluate(arena, jump) == {i: v for i, v in expected.items() if v}


@pytest.mark.parametrize("seed", [0, 1, 9, 18, 196, 292, 909, 1041, 1051, 1593])
def test_event_successor_equals_centered_successor_on_bounded_sources(
    seed: int,
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    digits = [int(d) for d in str(seed)[::-1]]
    pairs = [a + b for a, b in zip(digits, reversed(digits), strict=True)]
    delta = center_pair_field(arena, _polynomial(arena, pairs), extent=len(pairs))
    for _ in range(5):
        m = len(digits)
        carries: list[int] = []
        output: list[int] = []
        c = 0
        for i in range(m):
            c, digit = divmod(digits[i] + digits[-1 - i] + c, 10)
            carries.append(c)
            output.append(digit)
        if c:
            output.append(c)
        q = _polynomial(arena, carries)
        beta = reflected_innovation(
            arena, carry_coboundary(arena, q, base=10), extent=m, growth=c
        )
        expected = advance_centered_residual(arena, delta, beta, extent=m, growth=c)
        result = advance_centered_events(
            arena,
            event_difference(arena, delta),
            event_difference(arena, q),
            extent=m,
            growth=c,
        )
        assert _evaluate(arena, result) == _evaluate(
            arena, event_difference(arena, expected)
        )
        delta, digits = expected, output


def test_no_growth_neutral_field_is_not_temporal_identity() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    result = advance_centered_events(arena, arena.zero, arena.zero, extent=3, growth=0)
    assert _evaluate(arena, result) == {0: 9, 3: -9}


def test_failed_normalization_releases_temporary_work_and_rejects_foreign_inputs() -> (
    None
):
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    expression = arena.interval(10**200)
    before = ledger.entries, ledger.nodes
    ledger.tighten_limits(ledger.nodes + 1, None)
    with pytest.raises(BlockContextBudgetExceeded):
        event_difference(arena, expression)
    assert (ledger.entries, ledger.nodes) == before
    assert audit_registered_payloads(ledger).unknown_payloads == 0
    foreign = SymbolicInnovationArena(ResourceLedger())
    owners = ledger.owner_count
    with pytest.raises(ValueError):
        event_difference(arena, foreign.zero)
    assert ledger.owner_count == owners
