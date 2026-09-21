"""Exact affine Frobenius products for executed reverse/add observations."""

from __future__ import annotations

from random import Random

import pytest

from devtools.experiments.reverse_add.frobenius_sectors import (
    ReverseFrobeniusSectorProduct,
)
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
)
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    ReverseFrobeniusPlan,
)
from tests.support.reverse_sector_reference import (
    from_annihilated_source,
    from_endpoint_sectors,
)


def test_observed_product_projects_and_composes_every_sector() -> None:
    first = ReverseFrobeniusSectorProduct.atom(
        (1, 2, 3),
        0,
        maximum_classes=8,
        bits=5,
    )
    second = ReverseFrobeniusSectorProduct.atom(
        (3, 1, 4),
        1,
        maximum_classes=8,
        bits=5,
    )
    composed = first.then(second)
    assert tuple(block.order for block in composed.sectors) == (2, 4, 8, 16)
    assert composed.steps == 2
    assert composed.growth == 1
    for block, order in zip(composed.sectors, (2, 4, 8, 16), strict=True):
        direct = ReverseAddCyclotomicInnovationBlock.from_events(
            ((1, 2, 3), (3, 1, 4)),
            (0, 1),
            order=order,
            bits=5,
        )
        assert block.canonical_key == direct.canonical_key


def test_observed_product_composition_is_associative_and_canonical() -> None:
    atoms = tuple(
        ReverseFrobeniusSectorProduct.atom(
            event,
            growth,
            maximum_classes=4,
            bits=5,
        )
        for event, growth in (((1,), 0), ((2,), 1), ((3,), 0))
    )
    left = atoms[0].then(atoms[1]).then(atoms[2])
    right = atoms[0].then(atoms[1].then(atoms[2]))
    assert left == right
    assert left.canonical_key == right.canonical_key
    assert all(block.compositions == 0 for block in left.sectors)


def test_saturated_equal_affine_effects_drop_temporal_provenance_from_identity() -> (
    None
):
    atom = ReverseFrobeniusSectorProduct.atom(
        (0,),
        0,
        maximum_classes=4,
        bits=5,
    )
    five = ReverseFrobeniusSectorProduct.identity(maximum_classes=4, bits=5)
    for _ in range(5):
        five = five.then(atom)
    six = five.then(atom)
    assert five.steps == 5
    assert six.steps == 6
    assert five.canonical_key == six.canonical_key


def test_observed_product_rejects_numeric_aliases() -> None:
    with pytest.raises(TypeError):
        ReverseFrobeniusSectorProduct.atom(
            (1, True),
            0,
            maximum_classes=4,
            bits=5,
        )
    with pytest.raises(TypeError):
        ReverseFrobeniusSectorProduct.atom(
            (1,),
            True,
            maximum_classes=4,
            bits=5,
        )
    with pytest.raises(ValueError, match="bounded local stencil"):
        ReverseFrobeniusSectorProduct.atom(
            (1,) * 9,
            0,
            maximum_classes=8,
            bits=5,
        )
    with pytest.raises(ValueError, match="signed limb"):
        ReverseFrobeniusSectorProduct.atom(
            (1 << 63,),
            0,
            maximum_classes=8,
            bits=5,
        )


def _multiply(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    """Independent multiplication modulo (z**m+1,32), used only as an oracle."""
    width = len(left)
    result = [0] * width
    for i, first in enumerate(left):
        for j, second in enumerate(right):
            degree = i + j
            result[degree % width] += first * second * (-1 if degree >= width else 1)
    return tuple(value % 32 for value in result)


def _carry_summary(values: tuple[int, ...]) -> ReverseCarrySectorTransfer:
    result = ReverseCarrySectorTransfer.leaf(10, values[0])
    for value in values[1:]:
        result = result.then(ReverseCarrySectorTransfer.leaf(10, value))
    return result


def _reduce(values: tuple[int, ...], classes: int) -> tuple[int, ...]:
    result = [0] * classes
    for index, value in enumerate(values):
        quotient, target = divmod(index, classes)
        result[target] = (result[target] + (-value if quotient & 1 else value)) % 32
    return tuple(result)


def test_carry_transfer_constructs_one_step_product_without_event_input() -> None:
    source = (7, 18, 7)
    target, growth = pair_step(source, 10)
    product = ReverseFrobeniusSectorProduct.from_carry_transfer(_carry_summary(source))
    assert product.growth == growth
    assert (
        "event" not in ReverseFrobeniusSectorProduct.from_carry_transfer.__annotations__
    )
    for block in product.sectors:
        transported = _multiply(
            block.radial.multiplier_residue(),
            _reduce(source, block.classes),
        )
        assert tuple(
            (value + forcing) % 32
            for value, forcing in zip(transported, block.innovation, strict=True)
        ) == _reduce(target, block.classes)


def test_endpoint_sector_product_recovers_affine_block_without_event_tape() -> None:
    source = (7, 18, 7)
    middle, _ = pair_step(source, 10)
    target, _ = pair_step(middle, 10)
    product = from_endpoint_sectors(
        _carry_summary(source),
        _carry_summary(middle),
        2,
    )
    assert product.growth == len(target) - len(source)
    for block in product.sectors:
        transported = _multiply(
            block.radial.multiplier_residue(),
            _reduce(source, block.classes),
        )
        assert tuple(
            (value + forcing) % 32
            for value, forcing in zip(transported, block.innovation, strict=True)
        ) == _reduce(target, block.classes)


@pytest.mark.parametrize("steps", (20, 21, 40, 41, 64))
def test_annihilated_product_needs_source_extent_only(steps: int) -> None:
    source = (7, 18, 7)
    final_input: tuple[int, ...] = source
    for _ in range(steps - 1):
        final_input, _ = pair_step(final_input, 10)
    target, _ = pair_step(final_input, 10)
    summary = _carry_summary(final_input)
    product = from_annihilated_source(
        len(source),
        summary,
        ReverseFrobeniusPlan.for_steps(
            maximum_classes=8,
            bits=5,
            steps=steps,
            growth_certificate=DECIMAL_REVERSE_GROWTH_CERTIFICATE,
        ),
    )
    assert product == from_endpoint_sectors(_carry_summary(source), summary, steps)
    assert product.growth == len(target) - len(source)
    assert all(product.source_annihilated_sectors)
    for block in product.sectors:
        assert block.innovation == _reduce(target, block.classes)


def test_annihilated_product_rejects_unproved_source_death() -> None:
    summary = _carry_summary((7, 18, 7))
    with pytest.raises(ValueError, match="not proved"):
        from_annihilated_source(
            3,
            summary,
            ReverseFrobeniusPlan.for_steps(
                maximum_classes=8,
                bits=5,
                steps=19,
                growth_certificate=DECIMAL_REVERSE_GROWTH_CERTIFICATE,
            ),
        )
    with pytest.raises(TypeError, match="exact integer"):
        from_annihilated_source(
            True,
            summary,
            ReverseFrobeniusPlan.for_steps(
                maximum_classes=8,
                bits=5,
                steps=20,
                growth_certificate=DECIMAL_REVERSE_GROWTH_CERTIFICATE,
            ),
        )


def test_balanced_sector_composition_matches_independent_ring_evolution() -> None:
    random = Random(196)
    for _ in range(12):
        events = tuple(
            (tuple(random.randrange(-8, 9) for _ in range(8)), random.randrange(2))
            for _ in range(8)
        )
        blocks = [
            ReverseFrobeniusSectorProduct.atom(event, growth, maximum_classes=8, bits=5)
            for event, growth in events
        ]
        while len(blocks) > 1:
            blocks = [blocks[i].then(blocks[i + 1]) for i in range(0, len(blocks), 2)]
        for sector in blocks[0].sectors:
            width = sector.classes
            initial = tuple(random.randrange(32) for _ in range(width))
            expected = initial
            for event, growth in events:
                shifted = (-expected[-1], *expected[:-1])
                transported = tuple(
                    value + shift if growth else 2 * value
                    for value, shift in zip(expected, shifted, strict=True)
                )
                forcing = [0] * width
                for degree, value in enumerate(event):
                    forcing[degree % width] += value * (
                        -1 if degree // width % 2 else 1
                    )
                expected = tuple(
                    (value + shift) % 32
                    for value, shift in zip(transported, forcing, strict=True)
                )
            transported = _multiply(sector.radial.multiplier_residue(), initial)
            actual = tuple(
                (value + shift) % 32
                for value, shift in zip(transported, sector.innovation, strict=True)
            )
            assert actual == expected
