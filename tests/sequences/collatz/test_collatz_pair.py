from number_compiler.sequences.collatz.pair import (
    accelerated_odd_collatz,
    accelerated_odd_target_mod3_from_valuation,
    collatz_valuation_itinerary,
    mul3_carry_monoid,
    mul3_digit_carry_fn,
    valuation_itinerary_slab,
)
from number_compiler.sequences.collatz.parity import CollatzParitySlab
from number_compiler.sequences.collatz.raw_field import CollatzRawDigitField


def test_decimal_mul3_digit_carries_form_exact_five_element_monoid() -> None:
    monoid = mul3_carry_monoid()
    outputs = {fn.outputs for fn in monoid}
    assert outputs == {
        (0, 0, 0),
        (0, 1, 1),
        (1, 1, 1),
        (1, 1, 2),
        (2, 2, 2),
    }
    for a in monoid:
        for b in monoid:
            assert a.after(b).outputs in outputs
    assert {mul3_digit_carry_fn(d, base=10).outputs for d in range(10)} == outputs


def test_collatz_decimal_pair_field_has_raw_max_28_and_ternary_carry_vector() -> None:
    seen_max = 0
    for n in (1, 3, 9, 27, 97, 999, 6171, 999999):
        field = CollatzRawDigitField.from_odd_value(n, base=10)
        assert field.represented_value() == 3 * n + 1
        assert all(c in (0, 1, 2) for c in field.normalization_carries())
        assert field.max_component <= 28
        seen_max = max(seen_max, field.max_component)
    assert CollatzRawDigitField.from_odd_value(9, base=10).max_component == 28
    assert seen_max == 28


def test_accelerated_collatz_retains_only_the_latent_valuation_not_nested_lanes() -> (
    None
):
    import number_compiler

    assert not hasattr(number_compiler, "valuation_lane_residue")
    assert not hasattr(number_compiler, "valuation_from_nested_divisibility")
    for odd in range(1, 1000, 2):
        step = accelerated_odd_collatz(odd)
        # Independent arithmetic guard for the canonical v2 extraction.
        m = 3 * odd + 1
        assert m % (1 << step.valuation) == 0
        assert m % (1 << (step.valuation + 1)) != 0
        assert step.target & 1
        assert step.target % 3 == accelerated_odd_target_mod3_from_valuation(
            step.valuation
        )


def test_valuation_itinerary_is_run_length_collatz_parity_coordinate_for_seed27() -> (
    None
):
    vals = collatz_valuation_itinerary(27)
    assert len(vals) == 41
    assert sum(vals) == 70
    assert max(vals) == 5
    slab = valuation_itinerary_slab(vals)
    assert isinstance(slab, CollatzParitySlab)
    assert slab.width == 70
    assert slab.ones == 41
    # The composed accelerated slab maps seed 27 directly to the final odd state 1.
    assert slab.apply(27) == 1


def test_valuation_slab_matches_stepwise_accelerated_odd_collatz() -> None:
    for seed in (3, 7, 27, 97, 871):
        value = seed
        vals = []
        for _ in range(12):
            if value == 1:
                break
            step = accelerated_odd_collatz(value)
            vals.append(step.valuation)
            value = step.target
        slab = valuation_itinerary_slab(vals)
        assert slab.apply(seed) == value


def test_prime_field_residue_of_whole_collatz_slab_is_one_affine_map() -> None:
    from number_compiler.sequences.collatz.pair import collatz_slab_mod_odd

    vals = collatz_valuation_itinerary(27)
    whole = valuation_itinerary_slab(vals[:12])
    # Exact integer application and each odd finite-field projection agree.
    target = whole.apply(27)
    for modulus in (5, 7, 11, 13, 31, 101):
        affine = collatz_slab_mod_odd(whole, modulus)
        assert affine.apply(27) == target % modulus
    # Projection commutes with slab composition.
    a = valuation_itinerary_slab(vals[:6])
    b = valuation_itinerary_slab(vals[6:12])
    for modulus in (5, 13, 31):
        assert collatz_slab_mod_odd(a, modulus).then(
            collatz_slab_mod_odd(b, modulus)
        ) == collatz_slab_mod_odd(a.then(b), modulus)


def test_collatz_raw_field_is_the_only_mul3_semantic_coordinate() -> None:
    field = CollatzRawDigitField.from_odd_value(27, base=10)
    assert set(field.__dataclass_fields__) == {"base", "coefficients"}
    assert field.source_digits()
    assert field.normalization_carries()[0] == 0
    assert field.represented_value() == 82


def test_mul3_carry_monoid_is_synthesized_from_radix_and_stays_five_state() -> None:
    want = {
        (0, 0, 0),
        (0, 1, 1),
        (1, 1, 1),
        (1, 1, 2),
        (2, 2, 2),
    }
    for base in (4, 10, 16, 64, 256):
        monoid = mul3_carry_monoid(base)
        assert {fn.outputs for fn in monoid} == want


def test_shared_collatz_mul3_carry_symmetry_is_exact_and_cached_by_orbit() -> None:
    from number_compiler.arithmetic.automata.symmetry_powering import (
        ActionTransform,
        OrientedFiniteActionArena,
    )
    from number_compiler.arithmetic.carry.carry_symmetry import (
        collatz_mul3_carry_kernel,
        collatz_mul3_carry_word_action,
    )

    kernel = collatz_mul3_carry_kernel(10)
    kernel.verify_conjugacy()
    arena = OrientedFiniteActionArena(kernel)
    word = (1, 9, 2, 7, 0, 4)
    mirror = collatz_mul3_carry_word_action(tuple(reversed(word)), arena=arena)
    original = collatz_mul3_carry_word_action(word, arena=arena)
    conjugate = collatz_mul3_carry_word_action(tuple(9 - x for x in word), arena=arena)
    assert original.action_id == mirror.action_id == conjugate.action_id
    assert (original.transform ^ mirror.transform) & ActionTransform.MIRROR
    assert (original.transform ^ conjugate.transform) & ActionTransform.CONJUGATE
    for incoming in (0, 1, 2):
        direct = incoming
        for digit in word:
            direct = kernel.transition(direct, digit)
        assert arena.apply(original.ref, incoming) == direct
