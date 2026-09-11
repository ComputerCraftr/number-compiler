from devtools.experiments.power_numbers.terminal_frobenius_packet_rank import (
    small_hankel_rank_differential,
    terminal_linear_packet_rank_audit,
)


def test_folded_x_linear_packet_has_full_cyclotomic_hankel_rank_on_small_controls() -> (
    None
):
    for M in (2, 4, 8, 16):
        assert small_hankel_rank_differential(M) == M


def test_structural_rank_explodes_at_reduced_prime_decision_threshold_without_materialization() -> (
    None
):
    f5 = terminal_linear_packet_rank_audit("fermat", 5)
    assert f5.decision_required_local_v2 == 16
    assert f5.folded_degree_log2 == 15
    assert f5.exact_linear_rank == 1 << 15
    assert not f5.bounded_dimension_possible

    m13 = terminal_linear_packet_rank_audit("mersenne", 13)
    assert m13.decision_required_local_v2 == 5
    assert m13.folded_degree_log2 == 4
    assert m13.exact_linear_rank == 16
    assert not m13.bounded_dimension_possible

    structural = terminal_linear_packet_rank_audit("fermat", 16)
    assert structural.folded_degree_log2 == (1 << 15) - 1
    assert structural.exact_linear_rank.bit_length() == 1 << 15
