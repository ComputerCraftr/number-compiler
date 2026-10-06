from math import isqrt

from number_compiler.arithmetic.fields.congruence_automaton import (
    encode_periodic_mixed_radix,
    mixed_radix_morphism,
)
from number_compiler.sequences.prime.congruence import (
    FactoredPrimeAutomaton,
    compile_prime_block_factored_decision,
)


def test_factored_prime_automaton_accepts_exact_wheel_primes_without_prime_bitmap() -> (
    None
):
    automaton = FactoredPrimeAutomaton.build(isqrt(10_010_000))
    cases = {9_999_991: True, 10_000_019: True, 10_000_021: False}
    for value, want in cases.items():
        got, calls, morphism = automaton.classify_value(value, radix=2)
        assert got is want
        assert 1 <= calls <= automaton.wheel.group_count
        assert morphism.symbols == value.bit_length()


def test_factored_prime_candidate_random_access_is_logarithmic_in_index() -> None:
    automaton = FactoredPrimeAutomaton.build(isqrt(10_010_000))
    start = 9_999_993
    state, _ = automaton.state_from_value(start, radix=2)
    for index in (0, 1, 13, 64, 4096, 1 << 20):
        got, morphism = automaton.advance(state, index)
        assert got.residues == tuple((start + 2 * index) % m for m in automaton.moduli)
        assert morphism.compositions <= max(1, 2 * max(1, index.bit_length()))


def test_factored_prime_decision_automaton_builds_directly_from_congruence_state() -> (
    None
):
    start = 9_999_993
    binary = compile_prime_block_factored_decision(start, 4096, base_period=(2,))
    base4 = compile_prime_block_factored_decision(start, 4096, base_period=(4,))
    mixed = compile_prime_block_factored_decision(start, 4096, base_period=(4, 2, 8))
    assert (binary.summary_count, binary.summary_first) == (503, 13)
    assert (base4.summary_count, base4.summary_first) == (503, 13)
    assert (mixed.summary_count, mixed.summary_first) == (503, 13)
    # Base 4 is a robust direct-projector win in both retained description and
    # congruence-transition work; it is the production default.
    assert base4.decision_description_bits < binary.decision_description_bits
    assert base4.congruence_transitions < binary.congruence_transitions
    # Alternating radices can compress the retained decision language further,
    # but are charged separately because their transition work need not be best.
    assert mixed.decision_description_bits < base4.decision_description_bits


def test_factored_prime_decision_mixed_radix_is_not_a_post_bitmap_cache_hit() -> None:
    for length in (64, 256):
        got = compile_prime_block_factored_decision(
            9_999_993, length, base_period=(4, 2, 8)
        )
        assert got.domain_size == length
        assert got.summary_first == 13
        assert got.gcd_calls > 0
        assert got.congruence_transitions > 0


def test_periodic_mixed_radix_morphism_is_an_exact_coordinate_change() -> None:
    automaton = FactoredPrimeAutomaton.build(isqrt(10_010_000))
    value = 10_000_019
    for bases in ((2,), (2, 3), (2, 5), (3, 5), (2, 3, 5)):
        encoding = encode_periodic_mixed_radix(value, bases)
        assert encoding.value == value
        morphism = mixed_radix_morphism(automaton.moduli, encoding)
        state = morphism.apply(automaton.zero())
        assert state.residues == tuple(value % m for m in automaton.moduli)
