from number_compiler.projection.radix_decision import (
    RadixDecisionMetrics,
    bitmap_radix_decision_metrics,
    collatz_inverse_symbolic_decision_metrics,
    shared_radix_decision_metrics,
)
from number_compiler.sequences.collatz.parity import collatz_parity_inverse_residue
from number_compiler.sequences.prime.set import project_odd_prime_block


def _inverse_truth_metrics(width: int) -> RadixDecisionMetrics:
    outputs = tuple(
        collatz_parity_inverse_residue(word, width) for word in range(1 << width)
    )
    return shared_radix_decision_metrics(outputs, width, width, order="lsb")


def test_collatz_inverse_parity_map_has_large_radix_dag_reduction() -> None:
    width = 12
    metrics = _inverse_truth_metrics(width)
    assert metrics.nonterminal_nodes == 604
    assert metrics.distinct_roots == width
    assert metrics.nonterminal_nodes < (1 << width) // 6


def test_prime_projection_bitmap_has_radix_decision_redundancy_but_not_a_generator() -> (
    None
):
    projection = project_odd_prime_block(9_999_993, 4096)
    metrics = bitmap_radix_decision_metrics(projection.composite_mask, 12, order="lsb")
    assert metrics.nonterminal_nodes == 454
    assert metrics.nonterminal_nodes < 4096 // 8


def test_collatz_inverse_symbolic_dag_matches_truth_table_and_extends_without_enumeration() -> (
    None
):
    width = 12
    ordinary = _inverse_truth_metrics(width)
    symbolic = collatz_inverse_symbolic_decision_metrics(width)
    assert symbolic.nonterminal_nodes == ordinary.nonterminal_nodes == 604
    assert symbolic.distinct_roots == ordinary.distinct_roots == width
    assert symbolic.symbolic_states <= symbolic.residual_state_upper_bound

    # This width would require a 16-million-row truth table in the old probe.
    wider = collatz_inverse_symbolic_decision_metrics(24)
    assert wider.nonterminal_nodes == 62_874
    assert wider.symbolic_states == 68_049
    assert wider.symbolic_states <= wider.residual_state_upper_bound
