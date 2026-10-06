from number_compiler.arithmetic.fields.congruence_automaton import (
    FactoredCongruenceState,
)
from number_compiler.sequences.collatz.pair import (
    collatz_valuation_itinerary,
    valuation_itinerary_slab,
)
from number_compiler.sequences.collatz.parity import (
    CollatzInverseStreamingProgram,
    collatz_parity_inverse_residue,
    collatz_slab_padic3,
    compile_collatz_slab_factored,
)


def test_collatz_inverse_full_set_map_has_linear_streaming_arithmetic_program() -> None:

    for width in (8, 16, 32, 64):
        program = CollatzInverseStreamingProgram.build(width)
        words = (0, 1, (1 << width) - 1, ((1 << width) // 3))
        for word in words:
            assert program.apply(word) == collatz_parity_inverse_residue(word, width)
        assert program.symbol_steps == width
        assert program.state_bits == 2 * width
        assert program.program_description_bits < 2 * width + 16


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


def test_three_adic_radial_quotient_annihilates_old_source_at_precision() -> None:
    valuations = (1, 4, 2, 1, 3, 1, 2, 5)
    for precision in range(1, len(valuations) + 1):
        slab = valuation_itinerary_slab(valuations[:precision])
        affine = collatz_slab_padic3(slab, precision)
        radial = affine.radial_quotient
        assert radial.source_valuation == precision
        assert radial.source_annihilated
        assert radial.source_unit is None
        assert radial.as_affine().canonical_key == affine.canonical_key
