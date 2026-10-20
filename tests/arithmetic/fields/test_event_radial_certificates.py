"""Production radial-identity cancellation without atom or coefficient queries."""

from __future__ import annotations

from collections.abc import Callable
from random import Random
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields import event_innovation
from number_compiler.arithmetic.fields.event_innovation import normalize_event_sum
from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationID,
    RadialMultiplier,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from tests.support.symbolic_innovation import evaluate


def _identity(
    arena: SymbolicInnovationArena, atom: InnovationID, q: int, r: int
) -> InnovationID:
    low = arena.radial(atom, RadialMultiplier(q, r))
    high = arena.radial(atom, RadialMultiplier(q, r + 1))
    shifted = arena.chart(low, CylinderChart(1, -1))
    return arena.linear_combination(((1, high), (-1, low), (-1, shifted)))


@pytest.mark.parametrize("slope", [-1, 1])
@pytest.mark.parametrize("q", [0, 10**200])
def test_huge_radial_identity_cancels_without_evaluating_the_source_atom(
    slope: int, q: int
) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    atom = arena.atom(SemanticIdentity("formal-source", (196,)))
    expression = arena.chart(
        _identity(arena, atom, q, 10**200), CylinderChart(slope, 10**210)
    )
    assert normalize_event_sum(arena, expression) == arena.zero
    assert ledger.counters["event_radial_zero_blocks"] == 1
    assert ledger.counters["event_radial_cancelled_packets"] == 3
    assert ledger.counters["event_radial_certificate_terms"] <= 5
    assert "symbolic_innovation_projection_visits" not in ledger.counters
    audit = audit_registered_payloads(ledger)
    assert audit.unknown_payloads == audit.forbidden_future_payloads == 0


def test_different_source_atoms_cannot_cancel_from_matching_port_shapes() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    first = arena.atom(SemanticIdentity("formal-source", (196,)))
    other = arena.atom(SemanticIdentity("formal-source", (1,)))
    expression = arena.linear_combination(
        (
            (1, arena.radial(first, RadialMultiplier(0, 1))),
            (-1, first),
            (-1, arena.chart(other, CylinderChart(1, -1))),
        )
    )
    assert normalize_event_sum(arena, expression) != arena.zero


def test_exact_zero_block_cancels_before_a_distant_nonzero_event() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    one = arena.interval(1)
    distant = arena.chart(one, CylinderChart(1, -(10**200)))
    result = normalize_event_sum(arena, arena.add(_identity(arena, one, 0, 0), distant))
    assert result == distant


def test_nonzero_radial_block_preserves_the_exact_expression_handle() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    atom = arena.atom(SemanticIdentity("formal-source", (196,)))
    expression = arena.linear_combination(
        (
            (1, atom),
            (1, arena.radial(atom, RadialMultiplier(0, 10**200))),
            (1, arena.chart(atom, CylinderChart(1, -1))),
        )
    )
    assert normalize_event_sum(arena, expression) == expression
    assert ledger.counters["event_radial_certificate_blocks"] == 1
    assert ledger.counters.get("event_radial_zero_blocks", 0) == 0


def test_different_no_growth_powers_remain_separate_formal_groups() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    atom = arena.atom(SemanticIdentity("formal-source", (196,)))
    # This expression is mathematically zero, but cancellation across differing
    # 2-powers is intentionally outside the sparse growth certificate's scope.
    expression = arena.linear_combination(
        ((1, arena.radial(atom, RadialMultiplier(1, 0))), (-2, atom))
    )
    assert normalize_event_sum(arena, expression) == expression
    assert expression != arena.zero
    assert ledger.counters.get("event_radial_certificate_blocks", 0) == 0


def test_radial_certificate_normalization_matches_full_bounded_polynomials() -> None:
    random = Random(196)
    for _ in range(200):
        arena = SymbolicInnovationArena(ResourceLedger())
        terms: list[tuple[int, InnovationID]] = []
        for _ in range(random.randrange(1, 9)):
            value = arena.radial(
                arena.interval(random.randrange(1, 5)),
                RadialMultiplier(random.randrange(3), random.randrange(9)),
            )
            value = arena.chart(
                value, CylinderChart(random.choice((-1, 1)), random.randrange(-8, 9))
            )
            terms.append((random.randrange(-4, 5), value))
        expression = arena.linear_combination(terms)
        before = evaluate(arena, expression)
        result = normalize_event_sum(arena, expression)
        assert evaluate(arena, result) == before
        assert normalize_event_sum(arena, result) == result


def test_failed_radial_certificate_releases_all_temporary_ownership(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    expression = _identity(arena, arena.interval(1), 0, 4)
    before = ledger.entries, ledger.nodes
    original = cast(
        Callable[[event_innovation.EventWork, int], None],
        object.__getattribute__(event_innovation, "_certificate_reserve"),
    )

    def refuse_after_first_term(work: event_innovation.EventWork, bits: int) -> None:
        if ledger.counters.get("event_radial_certificate_terms", 0):
            raise BlockContextBudgetExceeded("injected certificate allocation failure")
        original(work, bits)

    monkeypatch.setattr(
        event_innovation, "_certificate_reserve", refuse_after_first_term
    )
    with pytest.raises(BlockContextBudgetExceeded, match="certificate"):
        normalize_event_sum(arena, expression)
    assert (ledger.entries, ledger.nodes) == before
    audit = audit_registered_payloads(ledger)
    assert audit.unknown_payloads == audit.forbidden_future_payloads == 0
