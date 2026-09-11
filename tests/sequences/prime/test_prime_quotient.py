from number_compiler.sequences.prime.quotient import (
    prime_block_summary_quotient,
    prime_count_quotient,
)
from number_compiler.sequences.prime.set import project_odd_prime_block


def test_hyperbolic_quotient_prime_counts_known_values() -> None:
    expected = {10: 4, 100: 25, 1_000: 168, 10_000: 1229, 100_000: 9592}
    for n, count in expected.items():
        result = prime_count_quotient(n)
        assert result.count == count
        assert result.quotient_states <= 2 * int(n**0.5) + 2


def test_hyperbolic_quotient_returns_same_block_summary_without_bitmap() -> None:
    start = 9_999_993
    for length in (16, 64, 256):
        quotient = prime_block_summary_quotient(start, length)
        bitmap = project_odd_prime_block(start, length)
        assert quotient.summary == bitmap.summary
        assert quotient.pi_queries <= 2 + length.bit_length()
