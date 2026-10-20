from dataclasses import replace
from typing import Never, cast

import pytest

from devtools.experiments.reverse_add import centered_future
from devtools.experiments.reverse_add.centered_future import (
    CenteredFutureGrammar,
    CenteredFutureState,
    CenteredFutureStateID,
    slp_polynomial,
)
from number_compiler.arithmetic.automata.residue_carry_slp import (
    ResidueCarrySLPProjector,
)
from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.fields.live_forcing import LiveForcingProjection
from number_compiler.resources.ledger import ResourceLedger
from tests.support.reference_carry import decimal_pair_carries


def _reference(seed: int, steps: int) -> tuple[int, ...]:
    for _ in range(steps):
        seed += int(str(seed)[::-1])
    return tuple(map(int, str(seed)[::-1]))


@pytest.mark.parametrize("seed", (0, 1, 18, 196, 909, 1041, 1051, 1593))
@pytest.mark.parametrize("steps", (0, 1, 2, 4))
def test_centered_future_matches_independent_bounded_orbit(
    seed: int, steps: int
) -> None:
    ledger = ResourceLedger()
    source = ExactSource(tuple(map(int, str(seed)[::-1])), 10, "reverse-add")
    grammar = CenteredFutureGrammar(ledger, source)
    state = grammar.construct(steps)
    view = grammar.state(state)
    actual = tuple(
        digit for start, stop, digit in grammar.runs(state) for _ in range(stop - start)
    )
    assert view.extent == len(actual)
    assert actual == _reference(seed, steps)
    assert ledger.counters.get("reverse_centered_future_advances", 0) == steps
    grammar.close()
    assert ledger.entries == ledger.nodes == 0


def test_default_twentieth_term_is_constructed_from_centered_cylinder() -> None:
    ledger = ResourceLedger()
    grammar = CenteredFutureGrammar(ledger, ExactSource((6, 9, 1), 10, "reverse-add"))
    state = grammar.construct(20)
    digits = tuple(
        digit for start, stop, digit in grammar.runs(state) for _ in range(stop - start)
    )
    assert digits == tuple(map(int, reversed("70446464506")))
    # This is an exact finite constructor, not a binary temporal pump.
    assert ledger.counters["reverse_centered_future_advances"] == 20
    grammar.close()
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("seed", (1, 196))
def test_centered_consumer_recovers_events_without_carry_grammar(
    seed: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("centered constructor rebuilt a carry word")

    monkeypatch.setattr(SLPArena, "__init__", forbidden)
    monkeypatch.setattr(centered_future, "slp_polynomial", forbidden)
    ledger = ResourceLedger()
    grammar = CenteredFutureGrammar(
        ledger, ExactSource(tuple(map(int, str(seed)[::-1])), 10, "reverse-add")
    )
    state = grammar.construct(20)
    actual = tuple(
        d for left, right, d in grammar.runs(state) for _ in range(right - left)
    )
    assert actual == _reference(seed, 20)
    assert ledger.counters["carry_event_domain_actions"] > 0
    assert ledger.counters["carry_event_reset_events"] > 0
    assert ledger.counters.get("live_carry_input_nodes", 0) == 0
    assert ledger.counters.get("reverse_centered_future_slp_nodes", 0) == 0
    # Spatial event recovery has not proved a temporal pump.
    assert ledger.counters["reverse_centered_future_advances"] == 20
    grammar.close()
    assert ledger.entries == ledger.nodes == 0


def test_carry_slp_repeat_becomes_logarithmic_symbolic_concatenation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    word = SLPArena()
    root = word.repeat(word.word((10, 9, 8)), 1 << 20)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("SLP polynomial conversion expanded its word")

    monkeypatch.setattr(SLPArena, "materialize", forbidden)
    ledger = ResourceLedger()
    grammar = CenteredFutureGrammar(ledger, ExactSource((1,), 10, "reverse-add"))
    before = grammar.arena.node_count
    projector = ResidueCarrySLPProjector(ledger)
    with projector.project(word, word.nodes[root]) as projected:
        expression = slp_polynomial(grammar.arena, projected, projected.outgoing_root)
        grammar.arena.resolve(expression)
    projector.close()
    assert grammar.arena.node_count - before < 100
    assert ledger.counters["residue_carry_slp_repeat_bits"] <= 21
    grammar.close()
    assert ledger.entries == ledger.nodes == 0


def test_centered_future_rejects_foreign_state() -> None:
    left = CenteredFutureGrammar(
        ResourceLedger(), ExactSource((6, 9, 1), 10, "reverse-add")
    )
    right = CenteredFutureGrammar(
        ResourceLedger(), ExactSource((6, 9, 1), 10, "reverse-add")
    )
    with pytest.raises(ValueError, match="different arena"):
        left.advance(right.initial)
    forged = CenteredFutureState(
        999,
        left.state(left.initial).extent,
        left.state(left.initial).output,
        left.state(left.initial).output,
    )
    with pytest.raises(TypeError, match="scoped state ID"):
        left.advance(cast(CenteredFutureStateID, forged))
    with pytest.raises(ValueError, match="allocated range"):
        left.advance(replace(left.initial, local_id=999))
    left.close()
    right.close()


@pytest.mark.parametrize(
    "source",
    (
        ExactSource((1,), 10, "reverse-add", blank=9),
        ExactSource((1,), 10, "reverse-add", extent=2),
        ExactSource((1,), 10, "reverse-add", alphabet_size=19),
    ),
)
def test_centered_future_rejects_unimplemented_source_geometry(
    source: ExactSource,
) -> None:
    with pytest.raises(ValueError, match="canonical finite digit geometry"):
        CenteredFutureGrammar(ResourceLedger(), source)


def test_centered_future_initialization_budget_refusal_releases_every_owner() -> None:
    ledger = ResourceLedger(1, 1)
    with pytest.raises(BlockContextBudgetExceeded):
        CenteredFutureGrammar(ledger, ExactSource((6, 9, 1), 10, "reverse-add"))
    assert ledger.entries == ledger.nodes == 0


def test_centered_future_arena_refusal_releases_precharged_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()

    class RefusingArena:
        def __init__(self, received: ResourceLedger) -> None:
            assert received is ledger
            # One retained source authority plus two constant-size scan cursors
            # are charged before any source-derived expression is allocated.
            assert ledger.entries == 3
            assert ledger.nodes == 6
            raise RuntimeError("refuse after source preflight")

    monkeypatch.setattr(centered_future, "SymbolicInnovationArena", RefusingArena)
    with pytest.raises(RuntimeError, match="source preflight"):
        centered_future.CenteredFutureGrammar(
            ledger, ExactSource((6, 9, 1), 10, "reverse-add")
        )
    assert ledger.entries == ledger.nodes == 0


def test_carry_slp_polynomial_preserves_asymmetric_word_order() -> None:
    source_word = (10, 9, 8, 10, 9, 8, 10, 9, 8)
    word = SLPArena()
    root = word.repeat(word.word(source_word[:3]), 3)
    expected, carry = decimal_pair_carries(source_word)

    ledger = ResourceLedger()
    grammar = CenteredFutureGrammar(ledger, ExactSource((1,), 10, "reverse-add"))
    projector = ResidueCarrySLPProjector(ledger)
    with projector.project(word, word.nodes[root]) as projected:
        assert projected.final_carry == carry
        expression = slp_polynomial(grammar.arena, projected, projected.outgoing_root)
        with LiveForcingProjection(grammar.arena, expression) as view:
            runs = view.residue_runs(0, len(source_word))
        actual = [run.residue for run in runs for _ in range(run.stop - run.start)]
        assert actual == expected
    projector.close()
    grammar.close()
    assert ledger.entries == ledger.nodes == 0
