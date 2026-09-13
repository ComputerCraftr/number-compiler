from random import Random

import pytest

from devtools.proofs import exact_oracle
from devtools.proofs.carry_action_quotient import CarryThresholdSignature
from devtools.proofs.oracles.digit_power import (
    lucas_lehmer_digit_field,
    pepin_digit_field,
)
from devtools.proofs.oracles.special_primality import lucas_lehmer_test, pepin_test
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import (
    CollatzSequenceSpec,
    FermatSequenceSpec,
    MersenneSequenceSpec,
    PrimeBlockSequenceSpec,
    ReverseAddSequenceSpec,
)
from number_compiler.arithmetic.carry.carry_normalization import (
    RadixCarryAction,
    RadixCarryBlock,
    normalize_cyclic_block,
    normalize_negacyclic_block,
)
from number_compiler.arithmetic.fields.adic_morphism import (
    ValuationSensitivityMorphism,
    collatz_slab_padic3,
    fermat_shifted_square_sensitivity,
    mersenne_successor_2adic_sensitivity,
    mersenne_successor_padic2,
    prime_translation_sensitivity,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_radial_quotient,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    cyclic_binary_square_projection,
    karatsuba_square,
    negacyclic_binary_square_projection,
)
from number_compiler.sequences.collatz.parity import (
    collatz_parity_slab,
    collatz_parity_word,
)
from number_compiler.sequences.power_numbers.factor_morphism import (
    batched_special_factor_witness,
    fermat_factor_witness,
    mersenne_factor_witness,
)
from number_compiler.sequences.prime.lane_quotient import canonical_prime_base_period


def test_radix_carry_block_is_exact_and_composes() -> None:
    rng = Random(20)
    for base in (2, 3, 10, 16):
        coeffs = tuple(rng.randrange(-5, 20) for _ in range(17))
        block = RadixCarryBlock.from_coefficients(coeffs, base=base)
        raw = sum(c * base**i for i, c in enumerate(coeffs))
        assert block.raw_value == raw
        for incoming in (-7, -1, 0, 1, 9):
            q, r = divmod(raw + incoming, base ** len(coeffs))
            assert block.outgoing_carry(incoming) == q
            assert block.normalized_payload(incoming) == r
        left = RadixCarryBlock.from_coefficients(coeffs[:8], base=base)
        right = RadixCarryBlock.from_coefficients(coeffs[8:], base=base)
        assert left.then(right).canonical_key == block.canonical_key


def test_multivalued_radix_carry_action_quotients_raw_provenance_and_composes() -> None:
    left = RadixCarryBlock.from_coefficients((3, 7, -2, 5), base=2)
    right = RadixCarryBlock.from_coefficients((4, -1, 6), base=2)
    whole = left.then(right)
    lo, hi = -4, 12
    a = RadixCarryAction.from_block(left, incoming_min=lo, incoming_max=hi)
    b = RadixCarryAction.from_block(right, incoming_min=lo, incoming_max=hi)
    combined = a.then(b)
    direct = RadixCarryAction.from_block(whole, incoming_min=lo, incoming_max=hi)
    assert combined.outgoing == direct.outgoing
    # Raw values 0 and 1 are indistinguishable on this deliberately narrow
    # domain, proving that the action key forgets algebraically irrelevant raw
    # provenance rather than just renaming it.
    z0 = RadixCarryAction.from_block(
        RadixCarryBlock(2, 4, 0), incoming_min=0, incoming_max=0
    )
    z1 = RadixCarryAction.from_block(
        RadixCarryBlock(2, 4, 1), incoming_min=0, incoming_max=0
    )
    assert z0.canonical_key == z1.canonical_key


def test_multivalued_radix_carry_action_binary_power_matches_repeated_block() -> None:
    block = RadixCarryBlock.from_coefficients((1, 0, 0), base=2)
    action = RadixCarryAction.from_block(block, incoming_min=0, incoming_max=1)
    powered = action.power(9)
    repeated = RadixCarryBlock.identity(2)
    for _ in range(9):
        repeated = repeated.then(block)
    direct = RadixCarryAction.from_block(repeated, incoming_min=0, incoming_max=1)
    assert powered.outgoing == direct.outgoing
    assert powered.compositions <= 2 * (9).bit_length()


def test_end_around_carry_is_one_scalar_boundary_not_a_vector() -> None:
    for width in (4, 8, 13):
        scale = 1 << width
        for raw in (0, scale // 2, scale + 7, 5 * scale + 23):
            block = RadixCarryBlock(2, width, raw)
            cyc = normalize_cyclic_block(block)
            neg = normalize_negacyclic_block(block)
            assert cyc.residue == raw % (scale - 1)
            assert cyc.boundary_in == cyc.boundary_out
            assert neg.residue == raw % (scale + 1)
            assert neg.boundary_out == -neg.boundary_in


def test_cyclotomic_digit_square_fields_are_exact() -> None:
    rng = Random(21)
    for width in (5, 7, 13):
        modulus = (1 << width) - 1
        for _ in range(20):
            value = rng.randrange(modulus)
            assert (
                cyclic_binary_square_projection(value, width).residue
                == value * value % modulus
            )
    for width in (4, 8, 16):
        modulus = (1 << width) + 1
        for _ in range(20):
            value = rng.randrange(modulus)
            assert (
                negacyclic_binary_square_projection(value, width).residue
                == value * value % modulus
            )


def test_dense_karatsuba_field_is_asymptotically_subquadratic_in_charged_ops() -> None:
    values = (1,) * 256
    _, metrics = karatsuba_square(values, threshold=8)
    schoolbook_muls = 256 * 256
    schoolbook_adds = schoolbook_muls - (2 * 256 - 1)
    assert metrics.scalar_multiplications < schoolbook_muls
    assert (
        metrics.scalar_multiplications + metrics.coefficient_additions
        < schoolbook_muls + schoolbook_adds
    )


def test_square_kernel_uses_triangular_products_without_general_multiply(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.polynomials.digit_convolution as convolution

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError((args, kwargs))

    monkeypatch.setattr(convolution, "karatsuba_convolution", forbidden)
    product, metrics = convolution.karatsuba_square((1,) * 8, threshold=8)
    assert product == (1, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1)
    assert metrics.scalar_multiplications == 8 * 9 // 2
    assert metrics.scalar_multiplications < 8 * 8


def test_special_digit_power_is_independent_exact_projection_path() -> None:
    for p in (3, 5, 7, 11, 13, 17, 19, 31):
        got = lucas_lehmer_digit_field(p)
        ref = lucas_lehmer_test(p)
        assert (got.residue, got.passes, got.iterations) == (
            ref.residue,
            ref.passes,
            ref.iterations,
        )
    for n in range(1, 6):
        got = pepin_digit_field(n)
        pepin_reference = pepin_test(n)
        assert (got.residue, got.passes, got.iterations) == (
            pepin_reference.residue,
            pepin_reference.passes,
            pepin_reference.squarings,
        )


def test_special_digit_power_uses_shared_arithmetic_tile_without_legacy_convolution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.polynomials.digit_convolution as legacy
    from devtools.proofs.oracles import digit_power

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError((args, kwargs))

    monkeypatch.setattr(legacy, "cyclic_binary_square_add_projection", forbidden)
    monkeypatch.setattr(legacy, "negacyclic_binary_square_projection", forbidden)
    for row in (
        digit_power.lucas_lehmer_digit_field(13),
        digit_power.pepin_digit_field(4),
    ):
        assert row.arithmetic_tile_steps == row.iterations
        assert row.legacy_digit_convolution_calls == 0
        assert row.scheduler_compositions == 0


def test_special_factor_witnesses_power_exponent_coordinate_directly() -> None:
    for q in (641, 6700417):
        w = fermat_factor_witness(5, q)
        assert w.divides and w.stride_compatible and w.compositions == 5
    for q in (23, 89):
        w = mersenne_factor_witness(11, q)
        assert w.divides and w.stride_compatible
        assert w.compositions <= 2 * (11).bit_length()
    assert not fermat_factor_witness(5, 643).divides
    assert not mersenne_factor_witness(11, 47).divides


def test_batched_special_factor_product_shares_power_across_sqrt_window() -> None:
    f5 = batched_special_factor_witness("fermat", 5, 6)
    assert f5.composite_witness and f5.proper_factor == 641 and f5.witness_k == 5
    assert f5.powered_compositions == 5
    assert f5.product_multiplications == 5
    assert f5.product_depth == 3
    # M11 has two factors in the first four slots; the root gcd is the whole
    # number, but product-tree descent still returns one proper divisor.
    m11 = batched_special_factor_witness("mersenne", 11, 4)
    assert m11.gcd_value == 2047
    assert m11.composite_witness and m11.proper_factor == 23
    assert m11.powered_compositions <= 2 * (11).bit_length()
    # Window exhaustion remains fail-closed.
    assert not batched_special_factor_witness("fermat", 4, 4).composite_witness
    assert not batched_special_factor_witness("mersenne", 13, 4).composite_witness


def test_tropical_sensitivity_morphisms_are_closed_and_power_logarithmically() -> None:
    a = ValuationSensitivityMorphism(2, 16, 2, 1, 1)
    b = ValuationSensitivityMorphism(2, 16, 3, 2, 1)
    c = a.then(b)
    for v in range(17):
        assert c.apply(v) == b.apply(a.apply(v))
    powered = prime_translation_sensitivity(2, 16).power(1 << 20)
    assert powered.apply(0) == 0
    assert powered.compositions <= 21
    assert fermat_shifted_square_sensitivity(64).power(6).apply(1) == 64
    assert power_two_cyclotomic_radial_quotient(4, 3, 9, bits=8).scalar_v2 == 5


def test_exact_padic_collatz_and_mersenne_channels_forget_source_when_theorem_says_so() -> (
    None
):
    word = collatz_parity_word(27, 20)
    slab = collatz_parity_slab(word, 20)
    radial = collatz_slab_padic3(slab, precision=8).radial_quotient
    assert radial.source_valuation == min(8, slab.ones)
    m = mersenne_successor_padic2(8).power(8)
    assert m.source_annihilated
    assert {m.apply(x) for x in (0, 1, 17, 255)} == {255}
    assert mersenne_successor_2adic_sensitivity(8).power(8).annihilates_unit_difference


@exact_oracle()
def test_reverse_add_threshold_key_stores_only_half_for_real_pair_fields() -> None:
    pair = (2, 9, 14, 18, 14, 9, 2)
    sig = CarryThresholdSignature.from_pair(pair, base=10)
    assert sig.symmetric
    assert sig.low_mask.bit_count() + sig.high_mask.bit_count() <= len(pair)
    old_full_bits = (10).bit_length() + len(pair).bit_length() + 2 * len(pair)
    assert sig.description_bits < old_full_bits


def test_prime_radix_policy_is_static_and_work_oriented() -> None:
    assert canonical_prime_base_period(64) == (4,)
    assert canonical_prime_base_period(1023) == (4,)
    assert canonical_prime_base_period(1024) == (4, 8)
    assert canonical_prime_base_period(4096) == (4, 8)


def test_unified_compiler_retains_shared_sensitivity_and_digit_projection_interfaces() -> (
    None
):
    compiler = CanonicalSequenceCompiler()
    reverse = compiler.compile_diagnostic(ReverseAddSequenceSpec(196, 10, 24))
    collatz = compiler.compile_diagnostic(CollatzSequenceSpec(27, 6, 64))
    prime = compiler.compile_diagnostic(PrimeBlockSequenceSpec(9_999_993, 4096))
    fermat = compiler.compile_diagnostic(FermatSequenceSpec((5,), test_through=5))
    mersenne = compiler.compile_diagnostic(MersenneSequenceSpec((31,), test_through=31))
    assert len(reverse.cyclotomic_radial_modes) == 4
    assert collatz.normalized_padic_radial is not None
    assert prime.translation_sensitivity is not None
    assert prime.decision.base_period == (4, 8)
    assert fermat.terms[0].shifted_sensitivity is not None
    # Special source compilation is theorem-free; the exact factor witness is
    # available only behind the demand-driven theorem boundary.
    assert fermat.terms[0].projection_method == "deferred"
    assert fermat.terms[0].factor_witness is None
    assert fermat.terms[0].digit_projection is None
    f5 = compiler.resolve_special_theorem("fermat", 5)
    assert f5.projection_method.startswith("terminal-threshold:")
    assert f5.primality is not None
    assert f5.factor_witness is None and f5.primality.status == "unknown"
    assert f5.primality.specialization_raw_squarings == 0
    assert not f5.primality.decided and f5.primality.target_depth is None
    assert f5.source_guard.failure_bit is None
    # The historical packed factor projection remains an explicit opt-in tool;
    # it is no longer charged to the default theorem path.
    f5_factor = CanonicalSequenceCompiler().resolve_special_theorem(
        "fermat",
        5,
        use_factor_projection=True,
        use_terminal_certificate=False,
    )
    assert (f5_factor.projection_method, f5_factor.factor_witness) == (
        "factored_digit_witness",
        641,
    )
    assert mersenne.terms[0].successor_sensitivity is not None
    # Raw Lucas--Lehmer digit projection is now an independent differential
    # utility and is intentionally absent from compiler diagnostics.
    assert mersenne.terms[0].digit_projection is None
    assert mersenne.terms[0].primality is None
    m31 = compiler.resolve_special_theorem("mersenne", 31)
    assert m31.projection_method.startswith("terminal-threshold:")
    assert m31.primality is not None and m31.primality.status == "unknown"
    assert m31.primality.specialization_raw_squarings == 0
    assert not m31.primality.decided and m31.primality.target_depth is None
    assert m31.source_guard.failure_bit is None


@exact_oracle()
def test_reset_itinerary_is_extensional_carry_automaton_and_optimizer_selects_cheaper_encoding() -> (
    None
):
    from devtools.proofs.carry_action_quotient import (
        CarryResetSignature,
        analyze_carry_action_quotient,
    )
    from number_compiler.arithmetic.carry.carry_monoid import scan_carry_automaton

    pair = (2, 7, 7, 7, 7, 7, 7, 7, 2)
    reset = CarryResetSignature.from_pair(pair, base=8)
    assert (
        reset.boundaries(0) == scan_carry_automaton(pair, base=8, incoming=0).boundaries
    )
    assert (
        reset.boundaries(1) == scan_carry_automaton(pair, base=8, incoming=1).boundaries
    )
    octal = analyze_carry_action_quotient(196, base=8, transitions=128)
    assert octal.selected_signature_bits_average <= octal.threshold_bits_average
    assert octal.selected_signature_bits_average <= octal.reset_bits_average


def test_power_of_two_radix_collapses_special_digit_count_but_charges_coefficient_width() -> (
    None
):
    from number_compiler.sequences.power_numbers.radix_analysis import (
        fermat_power_radix_metrics,
        materialize_fermat_power_radix_digits,
        materialize_mersenne_power_radix_digits,
        mersenne_power_radix_metrics,
    )

    # Exact same integers, not digit-string reinterpretations.
    for k in (1, 2, 4, 8, 16):
        md = materialize_mersenne_power_radix_digits(31, k)
        fd = materialize_fermat_power_radix_digits(5, k)
        base = 1 << k
        assert sum(d * base**i for i, d in enumerate(md)) == (1 << 31) - 1
        assert sum(d * base**i for i, d in enumerate(fd)) == (1 << 32) + 1
    extreme_m = mersenne_power_radix_metrics(8191, 8191)
    extreme_f = fermat_power_radix_metrics(12, 1 << 12)
    assert extreme_m.digit_count == 1 and extreme_m.nonzero_digit_payload_bits == 8191
    assert extreme_f.digit_count == 2
    # The digit count collapsed, but the huge radix/coefficient is explicitly charged.
    assert extreme_f.radix_parameter_bits == 13
    assert extreme_m.exact_description_bits > extreme_m.radix_parameter_bits
