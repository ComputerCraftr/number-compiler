from __future__ import annotations

import pytest

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


def test_constant_right_jet_erases_earlier_effect_before_arithmetic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.polynomials.primary_jet as owner

    early = PrimaryJetAffineMorphism(5, 32, (7, 3, 1, 0, 8), (9, 3, 7, 5, 2), 100)
    later = PrimaryJetAffineMorphism.identity(5, 32)
    for e in (1, 2, 7, 3, 11):
        later = later.then(PrimaryJetAffineMorphism.binary_event(e, (e, 1, 2, 3, 4)))
    assert later.source_annihilated
    expected = later.apply(early.apply((1, 2, 3, 4, 5)))

    def forbidden(*_args: object, **_kwargs: object) -> tuple[int, ...]:
        raise AssertionError("dead inherited jet was multiplied")

    monkeypatch.setattr(owner, "_poly_mul", forbidden)
    result = early.then(later)
    assert result.steps == 105
    assert result.offset == expected
    assert result.apply((5, 4, 3, 2, 1)) == expected
    with pytest.raises(ValueError, match="incompatible"):
        early.then(PrimaryJetAffineMorphism(5, 5, (0,) * 5, (0,) * 5))
    with pytest.raises(ValueError):
        result.apply((0,))


def test_binary_squares_keep_new_births_after_inherited_source_dies() -> None:
    atom = PrimaryJetAffineMorphism.binary_event(3, (1, 2, 3, 4, 5))
    other = PrimaryJetAffineMorphism.binary_event(3, (2, 2, 3, 4, 5))
    for count in (1, 2, 4, 8, 16, 32, 64):
        action = atom.power(count)
        literal: tuple[int, ...] = (3, 1, 4, 1, 5)
        for _ in range(count):
            literal = atom.apply(literal)
        assert action.apply((3, 1, 4, 1, 5)) == literal
        assert action.source_annihilated == (count >= 5)
        if count >= 8:
            assert action.offset == atom.power(5).offset
            assert action.offset != other.power(count).offset
