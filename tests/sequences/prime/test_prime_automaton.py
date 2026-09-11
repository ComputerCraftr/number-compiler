from number_compiler.sequences.prime.automaton import (
    boolean_anf_metrics,
    boolean_coordinate_derivative_metrics,
    prime_cyclotomic_order_metrics,
    prime_lsb_residual_kernel,
)
from number_compiler.sequences.prime.set import project_odd_prime_block


def test_binary_prime_residual_kernel_does_not_merge_odd_prefixes_on_bounded_tail() -> (
    None
):
    for prefix_bits in range(1, 9):
        metrics = prime_lsb_residual_kernel(prefix_bits, 8)
        assert metrics.distinct_residuals == metrics.odd_prefixes


def test_prime_boolean_block_is_max_degree_not_affine() -> None:
    length = 4096
    projection = project_odd_prime_block(9_999_993, length)
    metrics = boolean_anf_metrics(projection.prime_mask, 12)
    assert metrics.degree == 12
    assert metrics.terms == 2060
    assert metrics.terms_by_degree[-1] == (12, 1)


def test_binary_cyclotomic_order_grouping_barely_compresses_prime_wheel() -> None:
    metrics = prime_cyclotomic_order_metrics(3163)
    assert metrics.generators == 447
    assert metrics.odd_generators == 446
    assert metrics.exact_order_groups == 413
    assert metrics.signed_order_groups == 387
    assert metrics.max_exact_group_size == 3
    assert metrics.max_signed_group_size == 4


def test_prime_boolean_block_has_no_constant_affine_coordinate_derivative() -> None:
    projection = project_odd_prime_block(9_999_993, 4096)
    metrics = boolean_coordinate_derivative_metrics(projection.prime_mask, 12)
    assert metrics.constant_derivatives == 0
    assert metrics.derivative_ones == (
        457,
        465,
        467,
        465,
        461,
        459,
        463,
        477,
        451,
        455,
        465,
        465,
    )
    assert metrics.pair_counts == (2048,) * 12
