from devtools.verification import exact_oracle
from number_compiler.arithmetic.carry.event_memory import forcing_event, pair_step
from number_compiler.arithmetic.fields.adic_morphism import collatz_slab_padic3
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_radial_quotient,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.sequences.collatz.pair import valuation_itinerary_slab


def test_power_two_radial_quotient_reconstructs_exact_cyclotomic_multiplier() -> None:
    for classes in (1, 2, 4, 8, 16):
        for q in range(6):
            for r in range(9):
                radial = power_two_cyclotomic_radial_quotient(classes, q, r, bits=5)
                direct = CyclotomicDigitBlock.from_coefficients(
                    (1,),
                    order=2 * classes,
                    modulus=32,
                ).reverse_add_linear_transport(no_growth=q, growth=r)
                assert radial.radial_exponent == q + r
                assert radial.multiplier_residue() == direct.residue


def test_reverse_add_innovation_composition_discards_multiplier_provenance() -> None:
    pair: tuple[int, ...] = (2, 9, 18, 9, 2)
    events = []
    growths = []
    for _ in range(8):
        target, growth = pair_step(pair, 10)
        events.append(forcing_event(pair, target, growth))
        growths.append(growth)
        pair = target
    for order in (2, 4, 8, 16):
        direct = ReverseAddCyclotomicInnovationBlock.from_events(
            events,
            growths,
            order=order,
            bits=5,
        )
        left = ReverseAddCyclotomicInnovationBlock.from_events(
            events[:3],
            growths[:3],
            order=order,
            bits=5,
        )
        right = ReverseAddCyclotomicInnovationBlock.from_events(
            events[3:],
            growths[3:],
            order=order,
            bits=5,
        )
        composed = left.then(right)
        assert composed.canonical_key == direct.canonical_key
        assert (
            composed.affine_morphism().canonical_key
            == direct.affine_morphism().canonical_key
        )


def test_collatz_three_adic_radial_quotient_annihilates_old_source_at_precision() -> (
    None
):
    valuations = (1, 4, 2, 1, 3, 1, 2, 5)
    for precision in range(1, len(valuations) + 1):
        slab = valuation_itinerary_slab(valuations[:precision])
        affine = collatz_slab_padic3(slab, precision)
        radial = affine.radial_quotient
        assert radial.source_valuation == precision
        assert radial.source_annihilated
        assert radial.source_unit is None
        assert radial.as_affine().canonical_key == affine.canonical_key


@exact_oracle()
def test_legacy_carry_shadow_adapters_are_absent() -> None:
    import number_compiler.sequences.collatz.pair as collatz_pair
    from devtools.verification import carry_action_quotient

    assert not hasattr(carry_action_quotient.CarryResetSignature, "cyclotomic_block")
    assert not hasattr(
        carry_action_quotient.CarryResetSignature, "event_cyclotomic_block"
    )
    assert not hasattr(collatz_pair, "collatz_mul3_carry_transducer")
    assert not hasattr(collatz_pair, "collatz_mul3_carry_cyclotomic")


def test_reverse_add_innovation_binary_power_matches_repeated_composition() -> None:
    events = ((1, 2, 1), (0, -1, 0), (2, 0, 2))
    growths = (1, 0, 1)
    block = ReverseAddCyclotomicInnovationBlock.from_events(
        events,
        growths,
        order=8,
        bits=6,
    )
    repeated = ReverseAddCyclotomicInnovationBlock.identity(order=8, bits=6)
    for _ in range(5):
        repeated = repeated.then(block)
    powered = block.power_block(5)
    assert powered.canonical_key == repeated.canonical_key
    assert (
        powered.affine_morphism().canonical_key
        == repeated.affine_morphism().canonical_key
    )
    assert powered.steps == 5 * block.steps
    assert powered.growth == 5 * block.growth


def test_live_padic_radial_quotient_roundtrips_source_unit_and_innovation() -> None:
    from number_compiler.arithmetic.fields.adic_morphism import PadicAffineMorphism

    affine = PadicAffineMorphism(3, 5, 18, 137, 7, 0)
    radial = affine.radial_quotient
    assert radial.source_valuation == 2
    assert not radial.source_annihilated
    assert radial.source_unit == 2
    assert radial.innovation == 137 % (3**5)
    assert radial.as_affine().canonical_key == affine.canonical_key


def test_joint_fixed_ring_innovation_uses_one_common_source_death_horizon() -> None:
    """Regression: Phi_2/Phi_4/Phi_8 may not stop at different suffixes."""
    from devtools.experiments.algebra.radial_innovation_quotients import (
        _live_reverse_symmetry_innovations_aligned,
        _symmetry_innovation_atom,
    )
    from number_compiler.arithmetic.formula.symmetry_frame import (
        FixedRealCyclotomicGerm,
        ReverseAddSymmetryInnovationBlock,
    )

    value = 1
    events = []
    growths = []
    widths = []
    for _ in range(9):
        digits = []
        x = value
        while x:
            digits.append(x % 10)
            x //= 10
        if not digits:
            digits = [0]
        pair = tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))
        target, growth = pair_step(pair, 10)
        events.append(forcing_event(pair, target, growth))
        growths.append(growth)
        widths.append(len(pair))
        value += int(str(value)[::-1])

    end = 7
    independent_horizons = []
    for order in (2, 4, 8):
        suffix = ReverseAddSymmetryInnovationBlock.identity(
            start_parity=widths[end] & 1,
            order=order,
            bits=5,
        )
        for start in range(end - 1, -1, -1):
            atom = _symmetry_innovation_atom(
                tuple(events[start]),
                growths[start],
                widths[start],
                order,
                5,
            )
            suffix = atom.then(suffix)
            if suffix.source_annihilated:
                independent_horizons.append(end - start)
                break

    assert independent_horizons == [2, 6, 7]
    aligned = _live_reverse_symmetry_innovations_aligned(
        tuple(events),
        tuple(growths),
        tuple(widths),
        end,
        orders=(2, 4, 8),
        bits=5,
    )
    assert aligned is not None
    views, live = aligned
    assert live == 7
    germ = FixedRealCyclotomicGerm.from_fixed_views(views, bits=5)
    assert germ.fixed_views == views
