import pytest

from devtools.experiments.antihydra.barrier_search import grammar_refinement
from devtools.experiments.antihydra.event_domain import (
    event_exponent_domain,
    source_event_exponent_domain,
)
from devtools.experiments.antihydra.future_grammar import (
    GrammarEdge,
    ReachableFutureGrammar,
)
from devtools.experiments.antihydra.source_safety import (
    SourceBlockID,
    SourceSafetyWorkspace,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    HalfOpenInterval as Interval,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.resources.ledger import ResourceLedger


def _literal_legal(interval: Interval, q: int) -> bool:
    ratio = Q(2**q, 3**q)
    return interval.upper > Q(2) * ratio and interval.lower < Q(3) * ratio


@pytest.mark.parametrize(
    "interval",
    (
        Interval(Q(0), Q(1, 10)),
        Interval(Q(1, 1000), Q(19, 100)),
        Interval(Q(1, 3), Q(4, 3)),
        Interval(Q(4, 3), Q(3, 2)),
        Interval(Q(7, 5), Q(8, 5)),
    ),
)
def test_exact_domain_matches_bounded_exhaustive_predicate(interval: Interval) -> None:
    domain = event_exponent_domain(interval, ResourceLedger())
    assert tuple(domain.contains(q) for q in range(1, 31)) == tuple(
        _literal_legal(interval, q) for q in range(1, 31)
    )


def test_zero_lower_endpoint_is_an_exact_unbounded_domain() -> None:
    domain = event_exponent_domain(Interval(Q(0), Q(1, 100)), ResourceLedger())
    assert domain.unbounded
    assert domain.first is not None and domain.first > 1
    assert domain.contains(10_000)


def test_strict_boundary_equalities_are_excluded() -> None:
    # At q=2 each strict test meets equality in one of these intervals.
    ratio = Q(4, 9)
    upper_equal = event_exponent_domain(Interval(Q(0), Q(2) * ratio), ResourceLedger())
    lower_equal = event_exponent_domain(
        Interval(Q(3) * ratio, Q(3, 2)), ResourceLedger()
    )
    assert not upper_equal.contains(2)
    assert not lower_equal.contains(2)


def test_source_bound_domain_matches_edge_guard_nonemptiness() -> None:
    ledger = ResourceLedger()
    workspace = SourceSafetyWorkspace(ledger, max_width=40)
    grammar = ReachableFutureGrammar(workspace, max_event=30)
    for width, residue in ((0, 0), (3, 1), (4, 5), (5, 11), (6, 17)):
        parent = workspace.cylinder(width, residue)
        domain = source_event_exponent_domain(workspace, parent)
        for q in range(1, 31):
            child = grammar.edge(parent, q).child
            assert domain.contains(q) == (not workspace.view(child).guard.empty)
    grammar.close()
    workspace.close()
    assert ledger.entries == ledger.nodes == 0


def test_search_refuses_before_constructing_over_budget_powers() -> None:
    ledger = ResourceLedger()
    with pytest.raises(BlockContextBudgetExceeded, match="operand-bit budget"):
        event_exponent_domain(
            Interval(Q(1, 1 << 500), Q(1, 1 << 499)),
            ledger,
            max_operand_bits=64,
        )
    assert ledger.counters["mahler_event_domain_refusals"] == 1


def test_research_search_prunes_before_constructing_empty_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = ReachableFutureGrammar.edge

    def guarded_edge(
        self: ReachableFutureGrammar, parent: SourceBlockID, exponent: int
    ) -> GrammarEdge:
        domain = source_event_exponent_domain(self.workspace, parent)
        assert domain.contains(exponent), "search constructed an excluded child"
        return original(self, parent, exponent)

    monkeypatch.setattr(ReachableFutureGrammar, "edge", guarded_edge)
    result = grammar_refinement(4, 4, 100_000)
    assert result["status"] == "FINITE_REACHABLE_GRAMMAR"
    records = result["records"]
    assert isinstance(records, list)
    assert [row["reachable_families"] for row in records] == [4, 12, 24, 48]
    work = result["work"]
    assert isinstance(work, dict)
    assert work["grammar_event_branches_pruned"] > 0
    assert result["larger_event_branches"] == "UNEXPLORED"
