"""Supplied carrier observations compose through the production F5 kernel."""

from dataclasses import replace
from typing import Never

import pytest

from devtools.experiments.reverse_add import powered_f5f2_carrier as reference
from devtools.experiments.reverse_add.powered_cocycle_regions import (
    TransitionGrammarAudit,
    split_class95,
    square_class95_words,
)
from number_compiler.arithmetic.fields.f5_innovation import compose_f5_forcing
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.arithmetic.polynomials.f5_transport import (
    F5AffineTransport,
    F5SpatialTransport,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.symbolic_innovation import evaluate, polynomial


@pytest.mark.parametrize("half", [4, 8, 16, 32, 64, 128, 256])
def test_supplied_blocks_square_through_d512(
    half: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    orbit = reference.reverse_add_pair_orbit(196, 2 * half)
    left = reference.powered_block(orbit, 0, half)
    right = reference.powered_block(orbit, half, half)
    full = reference.powered_block(orbit, 0, 2 * half)

    def classes(block: reference.PoweredCocycleBlock) -> tuple[int, ...]:
        return reference.cocycle_word(block)

    left_word, right_word, expected = classes(left), classes(right), classes(full)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("supplied forcing composition rescanned a decimal carrier")

    monkeypatch.setattr(reference, "reverse_add_pair_orbit", forbidden)
    monkeypatch.setattr(reference, "powered_block", forbidden)
    monkeypatch.setattr(reference, "carrier_coordinates", forbidden)
    monkeypatch.setattr(F5SpatialTransport, "shifts", forbidden)
    monkeypatch.setattr(F5SpatialTransport, "coefficient", forbidden)
    audit = TransitionGrammarAudit()
    result = square_class95_words(left_word, right_word, right, audit=audit)
    assert result == expected
    assert tuple(v // 5 for v in result) == tuple(v // 5 for v in right_word)
    passes = sum(m for _, m in right.f5_factors)
    width = right.target_width
    assert audit.shift_passes.total() == passes
    assert audit.shifted_cells == passes * width
    assert audit.added_cells == (passes + 1) * width
    assert audit.scaled_cells == audit.attached_cells == width
    assert audit.decoded_cells == left.target_width + width

    # The same known forcing also flows through actual production arithmetic
    # handles. Materializing the fixtures here is reference setup, not source
    # discovery by the constructor under test.
    arena = SymbolicInnovationArena(ResourceLedger())
    before = F5AffineTransport(
        F5SpatialTransport(left.no_growths, left.growths),
        polynomial(arena, list(left.f5_forcing)),
    )
    after = F5AffineTransport(
        F5SpatialTransport(right.no_growths, right.growths),
        polynomial(arena, list(right.f5_forcing)),
    )
    composed = compose_f5_forcing(arena, before, after)
    values = evaluate(arena, composed.forcing)
    assert tuple(values.get(i, 0) % 5 for i in range(width)) == full.f5_forcing
    assert not any(v % 5 for i, v in values.items() if not 0 <= i < width)
    arena.close()


def test_catalog_saturation_is_separate_from_cell_work() -> None:
    orbit = reference.reverse_add_pair_orbit(196, 64)
    audit = TransitionGrammarAudit()
    for half in (4, 8, 16, 32):
        for start in range(65 - 2 * half):
            left = reference.powered_block(orbit, start, half)
            right = reference.powered_block(orbit, start + half, half)
            words = tuple(reference.cocycle_word(b) for b in (left, right))
            square_class95_words(words[0], words[1], right, audit=audit)
    assert len(audit.add_rules) == 25
    assert len(audit.scale_rules) == 20
    assert len(audit.attach_rules) == 95
    assert audit.added_cells > 25
    assert audit.attached_cells > 95


def test_rejects_bad_classes_and_wrong_extent_or_f2_domain() -> None:
    for value in (-1, 95, True):
        with pytest.raises(ValueError):
            split_class95(value)
    for value in range(95):
        carrier, forcing = split_class95(value)
        assert 5 * carrier + forcing == value
        assert 0 <= carrier <= 18
    orbit = reference.reverse_add_pair_orbit(196, 8)
    right = reference.powered_block(orbit, 4, 4)
    with pytest.raises(ValueError, match="extents"):
        square_class95_words((), (), right)
    with pytest.raises(ValueError, match="annihilated"):
        square_class95_words((), (), replace(right, no_growths=0))


def test_carry_is_recovered_from_95_word_not_stored_in_its_alphabet(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry.carry_monoid import (
        CarryFn,
        apply_carry_fn,
        compose_carry_fn,
        value_carry_fn,
    )

    orbit = reference.reverse_add_pair_orbit(196, 32)
    block = reference.powered_block(orbit, 0, 32)
    coordinates = reference.carrier_coordinates(block)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("constructing the alphabet scanned carry")

    monkeypatch.setattr(reference, "carrier_coordinates", forbidden)
    word = reference.cocycle_word(block)
    assert word == tuple(row.reduced_cocycle_id for row in coordinates)
    prefix = CarryFn.ID
    for value, row in zip(word, coordinates, strict=True):
        symbol, _forcing = split_class95(value)
        assert apply_carry_fn(prefix, 0) == row.carry_in
        prefix = compose_carry_fn(value_carry_fn(symbol, 10), prefix)
        assert apply_carry_fn(prefix, 0) == row.carry_out
