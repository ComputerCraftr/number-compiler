from math import comb

from number_compiler.arithmetic.fields.projection_field import (
    binomial_moments_from_runs,
    binomial_moments_from_values,
    cyclotomic_jet_from_values,
    projection_field_summary_from_runs,
)
from number_compiler.sequences.prime.lane_quotient import (
    compile_prime_block_lane_quotient,
)
from number_compiler.sequences.prime.set import project_odd_prime_block


def test_binomial_projection_concatenation_matches_brute_moments() -> None:
    values = (2, 0, 3, 1, 4, 1, 0, 2)
    whole = binomial_moments_from_values(values, degree=5, modulus=64)
    brute = tuple(
        sum(comb(i, r) * v for i, v in enumerate(values)) % 64 for r in range(5)
    )
    assert whole.moments == brute
    split = binomial_moments_from_values(values[:3], degree=5, modulus=64).then(
        binomial_moments_from_values(values[3:], degree=5, modulus=64)
    )
    assert split.canonical_key == whole.canonical_key
    block = binomial_moments_from_runs(((7, 1_000_000),), degree=4, modulus=32)
    assert block.length == 1_000_000 and block.compositions < 64


def test_cyclotomic_projection_concatenation_and_power_are_exact() -> None:
    values = (1, 0, 1, 1, 0, 1, 0, 0, 1)
    for order in (2, 4, 8):
        whole = cyclotomic_jet_from_values(values, order=order, modulus=32)
        split = cyclotomic_jet_from_values(values[:4], order=order, modulus=32).then(
            cyclotomic_jet_from_values(values[4:], order=order, modulus=32)
        )
        assert split.canonical_key == whole.canonical_key
        atom = cyclotomic_jet_from_values((3,), order=order, modulus=32)
        powered = atom.power_block(1000)
        direct = cyclotomic_jet_from_values((3,) * 1000, order=order, modulus=32)
        assert powered.canonical_key == direct.canonical_key
        assert powered.compositions < 32


def test_projection_field_summary_keeps_million_symbol_run_symbolic() -> None:
    s = projection_field_summary_from_runs(((5, 1_000_000),), degree=4, modulus=32)
    assert s.length == 1_000_000 and s.run_count == 1
    assert s.word_nodes <= 1
    assert s.binomial_moments.compositions < 64


def test_prime_residual_dag_emits_output_algebra_without_bitmap() -> None:
    start, length = 9_999_993, 256
    q = compile_prime_block_lane_quotient(
        start, length, base_period=(4,), projection_algebra=True
    )
    explicit = project_odd_prime_block(start, length)
    bits = tuple(1 if (explicit.prime_mask >> i) & 1 else 0 for i in range(length))
    expected_b = binomial_moments_from_values(bits, degree=4, modulus=32)
    assert q.binomial_moments is not None
    assert q.binomial_moments.canonical_key == expected_b.canonical_key
    for block in q.cyclotomic_projection:
        assert (
            block.canonical_key
            == cyclotomic_jet_from_values(
                bits, order=block.order, modulus=32
            ).canonical_key
        )
    assert q.summary == explicit.summary


def test_prime_output_algebra_is_optional_and_charged() -> None:
    a = compile_prime_block_lane_quotient(9_999_993, 64, base_period=(4,))
    b = compile_prime_block_lane_quotient(
        9_999_993, 64, base_period=(4,), projection_algebra=True
    )
    assert a.binomial_moments is None and not a.cyclotomic_projection
    assert a.projection_field_compositions == 0
    assert b.projection_field_compositions > 0
    assert b.projection_work > a.projection_work
