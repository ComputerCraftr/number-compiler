"""Spatial projection and linear death do not imply nonlinear successor closure."""

from dataclasses import fields
from itertools import product

import pytest

from devtools.verification.collatz_harmonic_ports import (
    ZERO,
    Y,
    admitted_cylinder_symbols,
    binary_carry_birth,
    binary_jet,
    binary_output_response,
)
from devtools.verification.collatz_harmonic_ports import (
    Radix64OutputHarmonicAction as OutputAction,
)
from devtools.verification.collatz_harmonic_ports import (
    Radix64WireHarmonicAction as Action,
)
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetAffineMorphism,
    PrimaryJetBlock,
    _poly_add,
    _poly_mul,
)
from number_compiler.sequences.collatz.hensel_cylinders import HenselCylinder


def test_two_wire_projection_and_spatial_associativity() -> None:
    identity = Action.identity()
    leaves = [Action.digit(d) for d in (0, 21, 22, 42, 43)]
    assert identity.domain.outputs == (0, 1, 2)
    assert len({Action.digit(d).response_key for d in range(64)}) == 5
    assert {Action.digit(d) for d in range(64)} == set(leaves)
    for a, b, c in product(leaves, repeat=3):
        assert a.then(b).then(c) == a.then(b.then(c))
        assert a.then(b).domain == b.domain.after(a.domain)
        assert identity.then(a) == a.then(identity) == a
    # An identity carry action with emissions is not an empty emitter.
    assert leaves[1].lower.fn == identity.lower.fn
    assert leaves[1].lower != identity.lower


def test_radix64_harmonic_action_retains_phase_instead_of_exact_extent() -> None:
    assert tuple(field.name for field in fields(Action)) == (
        "phase",
        "lower",
        "upper",
    )
    identity = Action.identity()
    assert identity.phase == 0
    action = Action.from_digits(range(24))
    assert action.phase == 0
    assert action.canonical_key == (action.phase, action.lower, action.upper)
    # Eight zero cells contribute a complete vanishing period to the
    # five-coefficient response. Exact-width keys would miss this alias.
    assert Action.from_digits((0,)) == Action.from_digits((0,) * 9)
    with pytest.raises(ValueError):
        Action(8, identity.lower, identity.upper)


def test_two_cell_mealy_composition_matches_all_three_exact_carry_ports() -> None:
    z = PrimaryJetBlock.digit(0, degree=5, modulus=2).power
    # The leaf gate above covers all 64 digits and proves these five exact
    # cylinder representatives exhaustive. Check their 25 products, rather
    # than replaying 4096 pairs with identical all-port responses.
    for first_digit, second_digit in product((0, 21, 22, 42, 43), repeat=2):
        action = Action.digit(first_digit).then(Action.digit(second_digit))
        assert action.phase == 2
        for incoming in range(3):
            middle = (3 * first_digit + incoming) // 64
            outgoing = (3 * second_digit + middle) // 64
            lower = (int(incoming >= 1), int(middle >= 1))
            upper = (int(incoming == 2), int(middle == 2))
            assert action.domain.apply(incoming) == outgoing
            assert action.lower.emit(int(incoming >= 1)) == _poly_add(
                (lower[0], 0, 0, 0, 0),
                tuple(lower[1] * item for item in z),
                2,
            )
            assert action.upper.emit(int(incoming == 2)) == _poly_add(
                (upper[0], 0, 0, 0, 0),
                tuple(upper[1] * item for item in z),
                2,
            )


def test_output_harmonic_mealy_action_is_exact_and_phase_normalized() -> None:
    identity = OutputAction.identity()
    assert identity.then(identity) == identity
    z_bit = PrimaryJetBlock.digit(0, degree=5, modulus=2)
    assert z_bit.power_block(24).power == (1, 0, 0, 0, 0)
    assert all(
        z_bit.power_block(6 * phase).power != (1, 0, 0, 0, 0) for phase in range(1, 4)
    )
    # The output row has already stabilized; four more zero cells change only
    # occurrence extent, so the canonical action is an actual cache alias.
    assert OutputAction.from_digits((0,)) == OutputAction.from_digits((0,) * 5)
    with pytest.raises(ValueError):
        OutputAction(4, identity.rows)
    for first_digit, second_digit in product(range(64), repeat=2):
        pair_digits = (first_digit, second_digit)
        action = OutputAction.from_digits(pair_digits)
        assert action.phase == 2
        source = first_digit + 64 * second_digit
        for incoming in range(3):
            raw = 3 * source + incoming
            assert action.rows[incoming].outgoing == raw // 64**2
            assert action.rows[incoming].jet == binary_jet(raw % 64**2, 2)
    for sample_digits in ((0,) * 4, (21,) * 8, tuple(range(12))):
        action = OutputAction.from_digits(sample_digits)
        assert action.phase == len(sample_digits) % 4
        split = len(sample_digits) // 2
        assert (
            OutputAction.from_digits(sample_digits[:split]).then(
                OutputAction.from_digits(sample_digits[split:])
            )
            == action
        )


def test_binary_jet_identity_and_phase_units() -> None:
    z = PrimaryJetBlock.digit(0, degree=5, modulus=32).power
    inverse = (31,) * 5
    assert _poly_mul(z, inverse, 32) == (1, 0, 0, 0, 0)
    for n in (1, 15, 19, 27, 129, 385, 477, 797, 58723):
        e = v2_positive(3 * n + 1)
        assert PrimaryJetAffineMorphism.binary_event(e, binary_carry_birth(n)).apply(
            binary_jet(n)
        ) == binary_jet((3 * n + 1) >> e)
    # Changing from bit positions to radix-64 positions is a substitution,
    # not a rename of the fifth-order nilpotent coordinate.
    cell_power = PrimaryJetBlock.digit(0, degree=5, modulus=2).power_block(6).power
    cell_y = _poly_add(cell_power, (1, 0, 0, 0, 0), 2)
    assert cell_y == (0, 0, 1, 0, 1) and cell_y != Y


def test_five_step_linear_death_does_not_kill_source_dependent_births() -> None:
    outcomes = []
    for source in (1, 27):
        n = source
        combined = PrimaryJetAffineMorphism.identity(5, 32)
        for _ in range(5):
            e = v2_positive(3 * n + 1)
            combined = combined.then(
                PrimaryJetAffineMorphism.binary_event(e, binary_carry_birth(n))
            )
            n = (3 * n + 1) >> e
        assert combined.kernel == ZERO
        assert combined.apply(binary_jet(source)) == binary_jet(n)
        outcomes.append(combined.offset)
    assert outcomes[0] != outcomes[1]


def test_complete_output_response_includes_transported_source() -> None:
    for n in (*range(64), 129, 385, 477, 797, 58723):
        assert binary_output_response(n) == tuple(
            binary_jet(3 * n + c, modulus=2) for c in range(3)
        )


def test_hensel_admission_and_root_mismatch_are_distinct() -> None:
    root = HenselCylinder.from_root(12, 2, 5)
    assert admitted_cylinder_symbols(root) == (root.residue % 64,)
    # A forcing root is queried under an independent occurrence domain. Its
    # mismatches are valid event branches, not automatically inadmissible.
    assert len(admitted_cylinder_symbols(HenselCylinder(0, 0))) == 64
    events = {d: root.consume(d) for d in range(64)}
    assert sum(event.status == "match" for event in events.values()) == 1
    assert sum(event.status == "mismatch" for event in events.values()) == 63
    for bits in range(7):
        domain = HenselCylinder(bits, 3)
        assert admitted_cylinder_symbols(domain) == tuple(
            d for d in range(64) if domain.contains(d)
        )
    with pytest.raises(ValueError):
        PrimaryJetAffineMorphism.binary_event(-1, ZERO)


def test_all_odd_16_bit_sources_have_reported_inherited_kernel_counts() -> None:
    """Finite census of the homogeneous jet, not a source grammar certificate."""
    horizons = (1, 2, 4, 8, 16, 32, 64)
    kernels: dict[int, set[tuple[int, ...]]] = {k: set() for k in horizons}
    units: dict[int, tuple[int, ...]] = {}
    for source in range(1, 1 << 16, 2):
        value, valuation = source, 0
        for k in range(1, 65):
            numerator = 3 * value + 1
            gap = (numerator & -numerator).bit_length() - 1
            valuation += gap
            value = numerator >> gap
            if k not in kernels:
                continue
            if k >= 5:
                kernel = ZERO
            else:
                if valuation not in units:
                    units[valuation] = PrimaryJetAffineMorphism.binary_event(
                        valuation, ZERO
                    ).kernel
                # y^(k-1) times the canonical z^-valuation*y kernel.
                kernel = (0,) * (k - 1) + units[valuation][: 6 - k]
            kernels[k].add(kernel)
    assert {k: len(v) for k, v in kernels.items()} == {
        1: 16,
        2: 18,
        4: 2,
        8: 1,
        16: 1,
        32: 1,
        64: 1,
    }
    assert all(kernels[k] == {ZERO} for k in horizons if k >= 8)
