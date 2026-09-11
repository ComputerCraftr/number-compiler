"""One emitting owner, exact carry projections, and a temporal negative gate."""

from dataclasses import fields
from itertools import product

import pytest

from number_compiler.arithmetic.carry.carry_monoid import (
    apply_carry_fn,
    compose_carry_fn,
    scan_carry_automaton,
)
from number_compiler.arithmetic.carry.decimal_jet_cylinder import (
    DecimalCarryJetBlock as Block,
)
from number_compiler.arithmetic.carry.event_memory import (
    forcing_event_from_carry,
    pair_step,
)
from number_compiler.arithmetic.carry.jet_cylinder import JetPortCylinder, JetPortRow
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetBlock,
    primary_jet_from_digits,
)


def _jet(values: tuple[int, ...]) -> tuple[int, ...]:
    return primary_jet_from_digits(values, degree=5, modulus=32).jet


def test_decimal_leaf_cylinders_have_three_derived_domains() -> None:
    leaves = tuple(Block.digit(value) for value in range(19))
    assert len({leaf.cylinder for leaf in leaves}) == 3
    assert tuple(field.name for field in fields(JetPortCylinder)) == ("modulus", "rows")
    for value, leaf in enumerate(leaves):
        for incoming in (0, 1):
            assert leaf.cylinder.rows[incoming].outgoing == (value + incoming) // 10
            assert apply_carry_fn(leaf.domain, incoming) == (value + incoming) // 10


def test_decimal_clock_has_minimal_period_128_and_no_width_powering(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    atom = PrimaryJetBlock.digit(0, degree=5, modulus=32)
    identity = atom.power_block(0).power
    assert atom.power_block(128).power == identity
    assert all(atom.power_block(phase).power != identity for phase in range(1, 128))
    block = Block.identity()
    for width in (*range(256), 10**100):
        assert Block(width, block.cylinder).clock == atom.power_block(width).power

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("clock lookup repeated binary powering")

    monkeypatch.setattr(PrimaryJetBlock, "power_block", forbidden)
    assert Block(10**100, block.cylinder).clock == identity


def test_all_port_carries_resets_and_forcing_are_views_of_one_cylinder() -> None:
    # One representative per exact carry-port function covers every possible
    # carry track, including counterfactual incoming one and every growth exit.
    for width in range(1, 6):
        for pair in product((0, 9, 10), repeat=width):
            block = Block.from_pair(pair)
            for incoming in (0, 1):
                carry = scan_carry_automaton(pair, incoming=incoming).boundaries
                assert block.cylinder.rows[incoming].jet == _jet(carry[:-1])
                assert block.following_jet(incoming) == _jet(carry[1:])
                assert block.reset_jet(incoming) == _jet(
                    tuple(b - a for a, b in zip(carry, carry[1:]))
                )
                assert block.normalization_jet(incoming) == _jet(
                    tuple(a - 10 * b for a, b in zip(carry, carry[1:]))
                )
            carry = scan_carry_automaton(pair).boundaries
            assert block.forcing_jet() == _jet(forcing_event_from_carry(carry))


def test_spatial_composition_and_external_clock_are_associative() -> None:
    empty = Block.identity()
    for values in product((0, 9, 10), repeat=3):
        a, b, c = (Block.digit(value) for value in values)
        assert a.then(b).then(c) == a.then(b.then(c))
        assert empty.then(a) == a.then(empty) == a
        assert a.then(b).domain == compose_carry_fn(b.domain, a.domain)
        for incoming in (0, 1):
            middle = a.cylinder.rows[incoming].outgoing
            assert (
                a.then(b).cylinder.rows[incoming].outgoing
                == b.cylinder.rows[middle].outgoing
            )


@pytest.mark.parametrize("pair_a,pair_b", [((4,), (8,)), ((4, 4), (8, 8))])
def test_complete_counterfactual_cylinder_is_not_a_temporal_root(
    pair_a: tuple[int, ...],
    pair_b: tuple[int, ...],
) -> None:
    a, b = Block.from_pair(pair_a), Block.from_pair(pair_b)
    assert a == b  # Same width/clock AND every carry-port emission, not just E(0).
    for incoming in (0, 1):
        assert (
            scan_carry_automaton(pair_a, incoming=incoming).boundaries
            == scan_carry_automaton(pair_b, incoming=incoming).boundaries
        )
        assert a.normalization_jet(incoming) == b.normalization_jet(incoming)
    assert a.forcing_jet() == b.forcing_jet() == (0,) * 5
    next_a, _ = pair_step(pair_a, 10)
    next_b, _ = pair_step(pair_b, 10)
    assert Block.from_pair(next_a).cylinder.outputs == (0, 0)
    assert Block.from_pair(next_b).cylinder.outputs == (1, 1)


def test_symbolic_spatial_squaring_never_replays_a_pair_word(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    block = Block.digit(16)

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("spatial composition reconstructed source digits")

    monkeypatch.setattr(Block, "digit", forbidden)
    monkeypatch.setattr(Block, "from_pair", forbidden)
    for _ in range(80):
        block = block.then(block)
    assert block.width == 2**80
    assert block.cylinder.outputs == (1, 1)
    assert len(block.forcing_jet()) == 5


def test_cylinder_rejects_wrong_algebra_or_noncanonical_rows() -> None:
    identity = JetPortCylinder.identity(2)
    with pytest.raises(ValueError):
        JetPortCylinder(32, (JetPortRow(2, (0,) * 5), JetPortRow(0, (0,) * 5)))
    with pytest.raises(ValueError):
        identity.then(JetPortCylinder.identity(3), (1, 0, 0, 0, 0))
    with pytest.raises(ValueError):
        identity.then(identity, (33, 0, 0, 0, 0))
