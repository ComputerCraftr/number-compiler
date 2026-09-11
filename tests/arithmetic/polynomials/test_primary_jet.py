from __future__ import annotations

from number_compiler.arithmetic.carry.carry_itinerary import (
    zplus1_jet,
    zplus1_jet_advance,
)
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetAffineMorphism,
    PrimaryJetBlock,
    primary_jet_from_digits,
    primary_jet_from_runs,
)


def _runs(
    values: tuple[int, int, int, int, int, int, int, int, int, int, int, int],
) -> tuple[tuple[int, int], ...]:
    out: list[tuple[int, int]] = []
    for value in values:
        if out and out[-1][0] == value:
            out[-1] = (value, out[-1][1] + 1)
        else:
            out.append((value, 1))
    return tuple(out)


def test_primary_jet_rle_equals_expanded_reverse_add_coordinate() -> None:
    digits = (6, 9, 1, 1, 1, 0, 0, 7, 7, 7, 7, 2)
    explicit = primary_jet_from_digits(digits, degree=4, modulus=32)
    powered = primary_jet_from_runs(_runs(digits), degree=4, modulus=32)
    assert explicit.jet == powered.jet == zplus1_jet(digits, 4, 32)
    assert explicit.power == powered.power
    assert powered.length == len(digits)


def test_primary_jet_long_run_construction_is_logarithmic_not_one_node_per_digit() -> (
    None
):
    run = PrimaryJetBlock.digit(1, degree=4, modulus=32).power_block(1 << 20)
    assert run.length == 1 << 20
    assert run.compositions <= 21
    assert run.description_bits < 128


def test_primary_jet_affine_event_morphism_matches_existing_exact_advance() -> None:
    state = (1, 2, 3, 4)
    event = (2, 0, 1, 4, 3, 2)
    for growth in (0, 1):
        morphism = PrimaryJetAffineMorphism.reverse_add_event(
            event, growth, degree=4, modulus=32
        )
        assert morphism.apply(state) == zplus1_jet_advance(
            state, event, growth, modulus=32
        )


def test_primary_jet_affine_power_uses_binary_composition() -> None:
    atom = PrimaryJetAffineMorphism(4, 32, (1, 1, 0, 0), (1, 0, 0, 0), steps=1)
    powered = atom.power(1 << 16)
    assert powered.steps == 1 << 16
    assert powered.compositions <= 17


def test_square_tangent_kills_old_mod32_jet_after_five_transports() -> None:
    bases = (
        (1, 2, 3, 4, 5),
        (3, 1, 4, 1, 5),
        (7, 0, 2, 0, 1),
        (9, 8, 7, 6, 5),
        (11, 3, 0, 2, 1),
    )
    action = PrimaryJetAffineMorphism.identity(5, 32)
    for base in bases:
        action = action.then(
            PrimaryJetAffineMorphism.square_tangent(base, degree=5, modulus=32)
        )
    assert action.source_annihilated
    assert action.apply((1, 2, 3, 4, 5)) == action.apply((5, 4, 3, 2, 1))
    assert "steps" not in repr(action.canonical_key)
