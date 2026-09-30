import itertools

from devtools.verification.oracles.special_primality import (
    lucas_lehmer_test,
    pepin_test,
)
from number_compiler.arithmetic.carry.carry_itinerary import negacyclic_transport_kernel
from number_compiler.arithmetic.polynomials.cyclotomic import (
    cyclotomic_one_plus_norm,
    cyclotomic_two_adic_growth_channel,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_annihilated,
    power_two_cyclotomic_modulus,
    power_two_cyclotomic_transport,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    cyclic_binary_square_projection,
    negacyclic_binary_square_projection,
)
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
    fermat_factor_stride,
    fermat_number,
    fermat_previous_product,
    fermat_successor,
    mersenne_composite_exponent_factor,
    mersenne_factor_stride,
    mersenne_gcd_spec,
    mersenne_number,
    mersenne_successor,
)


def _v2(value: int, bits: int) -> int:
    value %= 1 << bits
    if value == 0:
        return bits
    return (value & -value).bit_length() - 1


def test_cyclotomic_plus_norm_classifies_two_adic_channels() -> None:
    expected = {
        1: 2,
        2: 0,
        3: 1,
        4: 2,
        5: 1,
        6: 3,
        8: 2,
        10: 5,
        12: 1,
        16: 2,
        18: 3,
        20: 1,
    }
    for order, norm in expected.items():
        assert cyclotomic_one_plus_norm(order) == norm
    assert cyclotomic_two_adic_growth_channel(2) == "zero"
    for order in (4, 8, 16, 32):
        assert cyclotomic_two_adic_growth_channel(order) == "ramified"
    for order in (3, 5, 6, 10, 12):
        assert cyclotomic_two_adic_growth_channel(order) == "unit"


def test_power_two_cyclotomic_closed_valuation_matches_expanded_negacyclic_kernel() -> (
    None
):
    bits = 5
    modulus = 1 << bits
    for classes in (2, 4, 8):
        assert power_two_cyclotomic_modulus(10, classes) == 10**classes + 1
        for q in range(6):
            for r in range(3 * classes + 2):
                closed = power_two_cyclotomic_transport(classes, q, r)
                kernel = negacyclic_transport_kernel(classes, q, r, modulus=modulus)
                got_annihilated = not any(kernel)
                assert closed.annihilated(bits) == got_annihilated
                assert (
                    power_two_cyclotomic_annihilated(classes, q, r, bits=bits)
                    == got_annihilated
                )
                if not got_annihilated:
                    assert min(_v2(x, bits) for x in kernel if x) == closed.scalar_v2
                    assert closed.scalar_v2 == q + r // classes
                    assert closed.remainder_growth == r % classes


def test_phi2_growth_channel_is_exact_reset() -> None:
    assert not power_two_cyclotomic_transport(1, 4, 0).exact_zero
    for growth in (1, 2, 100):
        assert power_two_cyclotomic_transport(1, 0, growth).exact_zero
        assert power_two_cyclotomic_annihilated(1, 0, growth, bits=100)


def test_fermat_and_mersenne_are_symbolically_tiny_cyclotomic_families() -> None:
    f = FermatNumberSpec(10)
    assert f.exponent == 1024
    assert f.cyclotomic_order == 2048
    assert f.bit_length == 1025
    assert f.description_bits <= 4
    m = MersenneNumberSpec(127)
    assert m.bit_length == 127
    assert m.description_bits == 7


def test_fermat_generation_is_squaring_after_subtracting_one_and_product_identity() -> (
    None
):
    values = [fermat_number(n) for n in range(6)]
    for a, b in itertools.pairwise(values):
        assert fermat_successor(a) == b
    product = 1
    for n, value in enumerate(values):
        if n:
            assert product == value - 2
        product *= value


def test_mersenne_generation_is_affine_after_adding_one() -> None:
    values = [mersenne_number(p) for p in range(1, 12)]
    for a, b in itertools.pairwise(values):
        assert mersenne_successor(a) == b


def test_pepin_known_first_composite_fermat_number() -> None:
    assert [pepin_test(n).passes for n in range(1, 6)] == [
        True,
        True,
        True,
        True,
        False,
    ]
    assert [pepin_test(n).squarings for n in range(1, 6)] == [1, 3, 7, 15, 31]


def test_lucas_lehmer_quadratic_unit_conjugacy_and_known_cases() -> None:
    for p in (3, 5, 7, 13, 17, 19, 31):
        result = lucas_lehmer_test(p)
        assert result.passes
        assert result.residue == 0
    for p in (11, 23):
        result = lucas_lehmer_test(p)
        assert not result.passes
        assert result.residue != 0

    # Independent theorem differential stays test-local: the production tree
    # no longer carries a second quadratic-extension multiplication type.
    for p in (5, 7, 11, 13):
        modulus = mersenne_number(p)
        a, b = 2, 1
        for _ in range(p - 2):
            a, b = (a * a + 3 * b * b) % modulus, (2 * a * b) % modulus
        assert (2 * a) % modulus == lucas_lehmer_test(p).residue


def test_special_factor_lanes_have_strong_forced_strides() -> None:
    # F_5 = 641 * 6700417; both factors are 1 mod 2**7.
    stride = fermat_factor_stride(5)
    assert 641 % stride == 1
    assert 6_700_417 % stride == 1
    # M_11 = 23 * 89; both factors are 1 mod 2*11.
    stride = mersenne_factor_stride(11)
    assert 23 % stride == 1
    assert 89 % stride == 1


def test_mersenne_cyclic_square_pair_field_is_exact() -> None:
    for p in (5, 7, 13):
        modulus = mersenne_number(p)
        for value in (0, 1, 3, 7, modulus // 3, modulus - 1):
            projection = cyclic_binary_square_projection(value, p)
            assert projection.residue == value * value % modulus


def test_fermat_negacyclic_square_pair_field_is_exact_including_minus_one_residue() -> (
    None
):
    for n in (2, 3, 4):
        modulus = fermat_number(n)
        for value in (0, 1, 3, modulus // 3, modulus - 2, modulus - 1):
            projection = negacyclic_binary_square_projection(value, 1 << n)
            assert projection.residue == value * value % modulus


def test_special_family_set_maps_have_exact_product_and_divisor_quotients() -> None:
    for n in range(6):
        assert fermat_previous_product(n) == fermat_number(n) - 2
    assert mersenne_gcd_spec(12, 18).exponent == 6
    factor = mersenne_composite_exponent_factor(15)
    assert factor is not None
    assert factor.exponent in (3, 5)
    assert mersenne_number(15) % factor.materialize() == 0
    assert mersenne_composite_exponent_factor(13) is None


def test_general_cyclotomic_coefficients_and_radix_reinterpretations_are_exact() -> (
    None
):
    from number_compiler.arithmetic.polynomials.cyclotomic import (
        cyclotomic_coefficients,
        polynomial_divisible_by_cyclotomic,
    )
    from number_compiler.sequences.power_numbers.numbers import (
        fermat_radix_reinterpretation,
        mersenne_radix_reinterpretation,
    )

    assert cyclotomic_coefficients(5) == (1, 1, 1, 1, 1)
    assert cyclotomic_coefficients(8) == (1, 0, 0, 0, 1)
    assert cyclotomic_coefficients(12) == (1, 0, -1, 0, 1)
    assert polynomial_divisible_by_cyclotomic((1, 1, 1, 1, 1), 5)
    for base in (2, 3, 5, 6, 10):
        f = fermat_radix_reinterpretation(3, base)
        assert f.cyclotomic_order == 16
        assert f.materialize() == base**8 + 1
        m = mersenne_radix_reinterpretation(5, base)
        assert m.cyclotomic_order == 5
        assert m.materialize() == (base**5 - 1) // (base - 1)
