from math import isqrt

from number_compiler.arithmetic.fields.congruence_automaton import (
    FactoredCongruenceState,
    FactoredPrimeAutomaton,
    compile_collatz_slab_factored,
    encode_periodic_mixed_radix,
    mixed_radix_morphism,
    reinterpret_binary_digits,
    undo_binary_digit_reinterpretation,
)
from number_compiler.sequences.collatz.pair import (
    collatz_valuation_itinerary,
    valuation_itinerary_slab,
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


def test_periodic_mixed_radix_morphism_is_an_exact_coordinate_change() -> None:
    automaton = FactoredPrimeAutomaton.build(isqrt(10_010_000))
    value = 10_000_019
    for bases in ((2,), (2, 3), (2, 5), (3, 5), (2, 3, 5)):
        encoding = encode_periodic_mixed_radix(value, bases)
        assert encoding.value == value
        morphism = mixed_radix_morphism(automaton.moduli, encoding)
        state = morphism.apply(automaton.zero())
        assert state.residues == tuple(value % m for m in automaton.moduli)


def test_binary_digit_reinterpretation_is_bijective_but_changes_arithmetic_value() -> (
    None
):
    value = 196
    for base in (3, 5, 10, 16):
        encoded = reinterpret_binary_digits(value, base)
        assert undo_binary_digit_reinterpretation(encoded, base) == value
        if base != 2:
            assert encoded != value


def test_collatz_whole_slab_projects_to_factored_odd_residues_with_powered_exponents() -> (
    None
):
    valuations = collatz_valuation_itinerary(27, max_odd_steps=100)
    slab = valuation_itinerary_slab(valuations)
    moduli = (5, 7, 11, 13, 17, 19, 23, 29, 31)
    projection = compile_collatz_slab_factored(slab, moduli)
    source = FactoredCongruenceState(tuple(27 % m for m in moduli))
    target = projection.morphism.apply(source)
    want = slab.apply(27)
    assert want == 1
    assert target.residues == tuple(want % m for m in moduli)
    assert projection.exponent_bit_work < 256


def test_factored_prime_decision_automaton_builds_directly_from_congruence_state() -> (
    None
):
    from number_compiler.arithmetic.fields.congruence_automaton import (
        compile_prime_block_factored_decision,
    )

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
    from number_compiler.arithmetic.fields.congruence_automaton import (
        compile_prime_block_factored_decision,
    )

    for length in (64, 256):
        got = compile_prime_block_factored_decision(
            9_999_993, length, base_period=(4, 2, 8)
        )
        assert got.domain_size == length
        assert got.summary_first == 13
        assert got.gcd_calls > 0
        assert got.congruence_transitions > 0


def test_collatz_inverse_full_set_map_has_linear_streaming_arithmetic_program() -> None:
    from number_compiler.sequences.collatz.parity import (
        CollatzInverseStreamingProgram,
        collatz_parity_inverse_residue,
    )

    for width in (8, 16, 32, 64):
        program = CollatzInverseStreamingProgram.build(width)
        words = (0, 1, (1 << width) - 1, ((1 << width) // 3))
        for word in words:
            assert program.apply(word) == collatz_parity_inverse_residue(word, width)
        assert program.symbol_steps == width
        assert program.state_bits == 2 * width
        assert program.program_description_bits < 2 * width + 16


def test_binary_reinterpretation_morphism_matches_reweighted_digit_integer() -> None:
    from number_compiler.arithmetic.fields.congruence_automaton import (
        binary_digit_reinterpretation_morphism,
    )

    moduli = (5, 7, 11, 13, 17, 19)
    zero = FactoredCongruenceState((0,) * len(moduli))
    for value in (17, 31, 257, 196):
        for base in (3, 5, 6, 10):
            morph = binary_digit_reinterpretation_morphism(moduli, value, base)
            got = morph.apply(zero).residues
            encoded = reinterpret_binary_digits(value, base)
            assert got == tuple(encoded % m for m in moduli)
