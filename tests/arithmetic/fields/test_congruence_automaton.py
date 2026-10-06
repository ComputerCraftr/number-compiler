from number_compiler.arithmetic.fields.congruence_automaton import (
    FactoredCongruenceState,
    binary_digit_reinterpretation_morphism,
    reinterpret_binary_digits,
    undo_binary_digit_reinterpretation,
)


def test_binary_digit_reinterpretation_is_bijective_but_changes_arithmetic_value() -> (
    None
):
    value = 196
    for base in (3, 5, 10, 16):
        encoded = reinterpret_binary_digits(value, base)
        assert undo_binary_digit_reinterpretation(encoded, base) == value
        if base != 2:
            assert encoded != value


def test_binary_reinterpretation_morphism_matches_reweighted_digit_integer() -> None:

    moduli = (5, 7, 11, 13, 17, 19)
    zero = FactoredCongruenceState((0,) * len(moduli))
    for value in (17, 31, 257, 196):
        for base in (3, 5, 6, 10):
            morph = binary_digit_reinterpretation_morphism(moduli, value, base)
            got = morph.apply(zero).residues
            encoded = reinterpret_binary_digits(value, base)
            assert got == tuple(encoded % m for m in moduli)
