from random import Random

import pytest

from number_compiler.sequences.collatz.parity import (
    CollatzParityCursor,
    CollatzParityTimeOperator,
    advance_collatz_parity,
    collatz_parity_inverse_residue,
    collatz_parity_inverse_residue_binomial,
    collatz_parity_word,
    normalized_collatz,
    physical_collatz,
    pow3_mod_pow2_binomial,
    summarize_parity_word,
    valid_physical_branch_count,
)


@pytest.mark.validation  # Exhaustive 2,046-residue dyadic-prefix bijection.
def test_parity_coordinate_is_bijection_on_every_finite_dyadic_prefix() -> None:
    for width in range(1, 11):
        seen = set()
        for residue in range(1 << width):
            word = collatz_parity_word(residue, width)
            seen.add(word)
            assert collatz_parity_inverse_residue(word, width) == residue
        assert len(seen) == 1 << width


def test_unknown_parity_itinerary_has_exact_linear_information_bound() -> None:
    from number_compiler.sequences.collatz.parity import (
        collatz_parity_information_bound,
    )

    for width in range(17):
        bound = collatz_parity_information_bound(width)
        assert bound.semantic_cases == 1 << width
        assert bound.minimum_itinerary_bits == width
        assert bound.itinerary_is_polylogarithmic_in_width == (width <= 1)


@pytest.mark.validation  # Exhaustive 8,190-word inverse implementation differential.
def test_parity_inverse_has_independent_binomial_implementation() -> None:
    for width in range(1, 13):
        for word in range(1 << width):
            assert collatz_parity_inverse_residue_binomial(
                word, width
            ) == collatz_parity_inverse_residue(word, width)


def test_three_power_binomial_transport_matches_modular_power() -> None:
    for bits in range(1, 10):
        modulus = 1 << bits
        for exponent in (0, 1, 2, 3, 5, 17, 64, 257, 4096):
            assert pow3_mod_pow2_binomial(exponent, bits) == pow(3, exponent, modulus)
            assert pow3_mod_pow2_binomial(exponent, bits, inverse=True) == pow(
                pow(3, exponent, modulus), -1, modulus
            )


def test_normalized_collatz_is_right_shift_in_parity_coordinate() -> None:
    rng = Random(0x51F7)
    for _ in range(256):
        n = rng.randrange(0, 1 << 20)
        width = rng.randrange(1, 18)
        lhs = collatz_parity_word(normalized_collatz(n), width)
        rhs = collatz_parity_word(n, width + 1) >> 1
        assert lhs == rhs


@pytest.mark.validation  # 256 random physical orbits of up to 127 steps.
def test_physical_collatz_power_is_weighted_rank_select_on_parity_stream() -> None:
    rng = Random(0xC011A72)
    for _ in range(256):
        seed = rng.randrange(1, 1 << 20)
        steps = rng.randrange(0, 128)
        # Every parity symbol costs at least one physical tick, so steps+1 bits
        # are enough to expose a possible pending odd symbol.
        width = steps + 2
        word = collatz_parity_word(seed, width)
        advanced = advance_collatz_parity(CollatzParityCursor(word, width), steps)

        direct = seed
        for _ in range(steps):
            direct = physical_collatz(direct)

        macro = seed
        for _ in range(advanced.consumed_symbols):
            macro = normalized_collatz(macro)
        decoded = macro if advanced.cursor.phase == 0 else 3 * macro + 1
        assert decoded == direct
        assert advanced.cursor.word == (word >> advanced.consumed_symbols)
        assert advanced.rank_queries <= max(0, width.bit_length()) + 6
        # Prefix selection uses cached 64-bit monoid blocks; only the final
        # constant-size leaf is inspected directly.
        assert advanced.rank_bits_scanned <= 64


def test_parity_duration_summary_is_associative_and_counts_physical_ticks() -> None:
    a = summarize_parity_word(0b10101, 5)
    b = summarize_parity_word(0b00111, 5)
    c = summarize_parity_word(0b10, 2)
    assert a.physical_steps == 8
    assert a.then(b).then(c) == a.then(b.then(c))
    assert a.then(b).physical_steps == a.physical_steps + b.physical_steps


def test_explicit_physical_branch_family_is_fibonacci_despite_constant_shift_suspension() -> (
    None
):
    assert [valid_physical_branch_count(n) for n in range(8)] == [
        1,
        2,
        3,
        5,
        8,
        13,
        21,
        34,
    ]
    assert valid_physical_branch_count(64).bit_length() > 40


def test_physical_time_operator_composes_by_addition_in_parity_coordinate() -> None:
    seed = 27
    width = 300
    word = collatz_parity_word(seed, width)
    cursor = CollatzParityCursor(word, width)
    a = CollatzParityTimeOperator(73)
    b = CollatzParityTimeOperator(91)
    sequential = b.apply(a.apply(cursor).cursor).cursor
    combined = a.then(b).apply(cursor).cursor
    assert sequential == combined
    huge = CollatzParityTimeOperator(1).power(1 << 1000)
    assert huge.operator_nodes == 1
    assert huge.description_bits == 1001


@pytest.mark.validation  # Exhaustive dyadic slabs, lifts, and normalized orbits.
def test_native_parity_slab_matches_inverse_residue_and_normalized_action() -> None:
    from number_compiler.sequences.collatz.parity import collatz_parity_slab

    for width in range(1, 11):
        for word in range(1 << width):
            slab = collatz_parity_slab(word, width)
            seed = collatz_parity_inverse_residue(word, width)
            assert slab.domain_residue == seed
            assert slab.ones == word.bit_count()
            for lift in (0, 1, 3):
                lifted = seed + (lift << width)
                value = lifted
                for _ in range(width):
                    value = normalized_collatz(value)
                assert collatz_parity_word(lifted, width) == word
                assert slab.apply(lifted) == value


def test_native_parity_slab_composition_is_associative_and_concat_exact() -> None:
    from number_compiler.sequences.collatz.parity import (
        CollatzParitySlab,
        collatz_parity_slab,
    )

    a = collatz_parity_slab(0b10101, 5)
    b = collatz_parity_slab(0b110, 3)
    c = collatz_parity_slab(0b1001, 4)
    assert a.then(b).then(c) == a.then(b.then(c))
    joined = 0b10101 | (0b110 << 5) | (0b1001 << 8)
    assert a.then(b).then(c) == collatz_parity_slab(joined, 12)
    assert CollatzParitySlab.identity().then(a) == a
    assert a.then(CollatzParitySlab.identity()) == a


@pytest.mark.validation  # Three complete valuation itineraries of up to 256 events.
def test_parity_word_reconstructs_exactly_from_existing_valuation_itinerary_without_replay() -> (
    None
):
    from number_compiler.sequences.collatz.pair import collatz_valuation_itinerary
    from number_compiler.sequences.collatz.parity import (
        collatz_parity_word,
        collatz_parity_word_from_valuations,
    )

    for seed in (27, 6171, 837799):
        vals = collatz_valuation_itinerary(seed, max_odd_steps=256)
        initial = seed
        even = 0
        while initial > 1 and not (initial & 1):
            initial >>= 1
            even += 1
        covered = even + sum(vals)
        width = min(128, covered)
        assert collatz_parity_word_from_valuations(
            seed, vals, width
        ) == collatz_parity_word(seed, width)


def test_run_compressed_valuation_schedule_matches_materialized_parity_cursor() -> None:
    from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
    from number_compiler.sequences.collatz.parity import (
        CollatzParityCursor,
        CollatzParityTimeOperator,
        CollatzValuationCursor,
        CollatzValuationSchedule,
        advance_collatz_parity,
        collatz_parity_word_from_valuations,
    )

    seed = 27
    value = seed
    valuations = []
    for _ in range(24):
        step = accelerated_odd_collatz(value)
        valuations.append(step.valuation)
        value = step.target
    width = sum(valuations)
    word = collatz_parity_word_from_valuations(seed, valuations, width)
    schedule = CollatzValuationSchedule(0, tuple(valuations))
    assert schedule.normalized_symbols == width
    assert schedule.physical_steps == width + len(valuations)

    for ticks in range(schedule.physical_steps + 1):
        old = advance_collatz_parity(CollatzParityCursor(word, width), ticks)
        new = CollatzParityTimeOperator(ticks).apply_valuations(
            CollatzValuationCursor(schedule),
        )
        assert new.position.consumed_normalized_symbols == old.consumed_symbols
        assert new.position.phase == old.cursor.phase
        assert new.cursor.physical_offset == ticks


def test_million_division_valuation_event_stays_one_schedule_entry() -> None:
    from number_compiler.sequences.collatz.parity import (
        CollatzParityTimeOperator,
        CollatzValuationCursor,
        CollatzValuationSchedule,
    )

    k = 1_000_000
    schedule = CollatzValuationSchedule(0, (k,))
    assert schedule.event_count == 1
    assert schedule.normalized_symbols == k
    assert schedule.physical_steps == k + 1
    assert schedule.description_bits < 64
    halfway = CollatzParityTimeOperator(500_000).apply_valuations(
        CollatzValuationCursor(schedule),
    )
    assert halfway.position.event_index == 0
    assert halfway.position.event_offset == 500_000
    assert halfway.position.consumed_normalized_symbols == 499_999
    assert halfway.event_binary_search_bound == 1
