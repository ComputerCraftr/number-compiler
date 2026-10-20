from __future__ import annotations

import itertools
import random

import pytest

from number_compiler.arithmetic.carry.event_memory import forcing_event, pair_step
from number_compiler.arithmetic.formula.symmetry_frame import (
    FixedRealCyclotomicGerm,
    ReverseAddSymmetryInnovationBlock,
    ReverseAddSymmetryLinearAction,
    ReverseAddSymmetryProjection,
)


def _palindrome(values: list[int] | tuple[int, ...], width: int) -> tuple[int, ...]:
    half = tuple(values)
    return half + tuple(reversed(half[: width // 2]))


def _add_mod(a: tuple[int, ...], b: tuple[int, ...], modulus: int) -> tuple[int, ...]:
    return tuple((x + y) % modulus for x, y in zip(a, b, strict=True))


def _projection(
    pair: tuple[int, ...], order: int, bits: int
) -> ReverseAddSymmetryProjection:
    projection = ReverseAddSymmetryProjection.from_coefficients(
        pair,
        order=order,
        bits=bits,
    )
    assert projection.inversion_fixed
    assert projection.removed_edge_factor == (len(pair) % 2 == 0)
    return projection


def _assert_involution(projection: ReverseAddSymmetryProjection) -> None:
    reflected = ReverseAddSymmetryProjection(
        projection.order,
        projection.bits,
        projection.width,
        projection.inversion_residue(),
    )
    assert reflected.inversion_residue() == projection.residue


def _assert_one_step_frame(
    pair: tuple[int, ...],
    *,
    base: int,
    order: int,
    bits: int,
    check_involution: bool = False,
) -> tuple[tuple[int, ...], int]:
    target, growth = pair_step(pair, base)
    event = forcing_event(pair, target, growth)
    source_projection = _projection(pair, order, bits)
    innovation_projection = _projection(event, order, bits)
    expected_projection = _projection(target, order, bits)
    if check_involution:
        for projection in (
            source_projection,
            innovation_projection,
            expected_projection,
        ):
            _assert_involution(projection)
    linear = ReverseAddSymmetryLinearAction(
        order,
        bits,
        1 - growth,
        growth,
    )
    actual = _add_mod(
        linear.apply_residue(
            source_projection.residue,
            start_parity=len(pair) & 1,
        ),
        innovation_projection.residue,
        1 << bits,
    )
    assert actual == expected_projection.residue
    return target, growth


@pytest.mark.validation
def test_symmetry_projection_is_inversion_fixed_and_removes_even_edge_factor() -> None:
    for base in range(3, 8):
        for width in range(1, 7):
            half = (width + 1) // 2
            for values in itertools.product(range(2 * base - 1), repeat=half):
                pair = _palindrome(values, width)
                _projection(pair, order=8, bits=5)


@pytest.mark.validation
def test_one_step_reverse_add_is_exact_in_the_reversal_fixed_frame_randomized() -> None:
    rng = random.Random(0x5A77E7)
    for base in range(3, 17):
        for _ in range(80):
            width = rng.randint(1, 20)
            half = [rng.randrange(2 * base - 1) for _ in range((width + 1) // 2)]
            pair = _palindrome(half, width)
            for order in (2, 4, 8, 16):
                _assert_one_step_frame(
                    pair,
                    base=base,
                    order=order,
                    bits=6,
                )


def test_symmetry_frame_small_cases_cover_sectors_growth_and_involution() -> None:
    cases = (
        ((9,), 0, 1),
        ((10,), 1, 1),
        ((9, 9), 0, 0),
        ((10, 10), 1, 0),
    )
    for pair, expected_growth, expected_parity in cases:
        assert (len(pair) & 1) == expected_parity
        for order in (2, 4, 8, 16):
            _target, growth = _assert_one_step_frame(
                pair,
                base=10,
                order=order,
                bits=6,
                check_involution=True,
            )
            assert growth == expected_growth


def test_growth_is_only_a_two_sector_symmetry_action() -> None:
    for order in (2, 4, 8, 16, 32):
        action = ReverseAddSymmetryLinearAction(order, 6, 0, 1)
        degree = order // 2
        one = (1,) + (0,) * (degree - 1)
        # odd width -> even width: the exact (1+z) edge factor is removed
        assert action.multiplier_residue(1) == one
        # even width -> odd width: the paired symmetry factor remains
        assert action.multiplier_residue(0) != one or order == 2
        assert action.end_parity(0) == 1
        assert action.end_parity(1) == 0


def test_symmetry_linear_action_composition_and_binary_power_are_exact() -> None:
    for order in (2, 4, 8, 16):
        left = ReverseAddSymmetryLinearAction(order, 7, 3, 5)
        right = ReverseAddSymmetryLinearAction(order, 7, 4, 2)
        combined = left.then(right)
        for parity in (0, 1):
            source = tuple((7 * i + 3) % 128 for i in range(order // 2))
            mid = left.apply_residue(source, start_parity=parity)
            direct = right.apply_residue(mid, start_parity=left.end_parity(parity))
            assert combined.apply_residue(source, start_parity=parity) == direct
        powered = left.power(13)
        assert powered.no_growth == 13 * left.no_growth
        assert powered.growth == 13 * left.growth
        assert powered.compositions <= 2 * (13).bit_length()


def test_symmetry_innovation_block_composes_contiguous_events_exactly() -> None:
    pair: tuple[int, ...] = (2, 9, 18, 9, 2)
    events: list[tuple[int, ...]] = []
    growths: list[int] = []
    widths: list[int] = []
    for _ in range(12):
        target, growth = pair_step(pair, 10)
        widths.append(len(pair))
        events.append(forcing_event(pair, target, growth))
        growths.append(growth)
        pair = target

    for order in (2, 4, 8, 16):
        direct = ReverseAddSymmetryInnovationBlock.from_events(
            events,
            growths,
            start_width=widths[0],
            order=order,
            bits=5,
        )
        split = 5
        left = ReverseAddSymmetryInnovationBlock.from_events(
            events[:split],
            growths[:split],
            start_width=widths[0],
            order=order,
            bits=5,
        )
        right = ReverseAddSymmetryInnovationBlock.from_events(
            events[split:],
            growths[split:],
            start_width=widths[split],
            order=order,
            bits=5,
        )
        composed = left.then(right)
        assert composed.canonical_key == direct.canonical_key
        assert (
            composed.affine_morphism().canonical_key
            == direct.affine_morphism().canonical_key
        )
        # Canonical identity stores only the inversion-fixed half coordinates.
        assert len(direct.fixed_innovation) <= len(direct.innovation)


def test_frame_flipping_affine_block_fails_honestly_on_self_power() -> None:
    # A sector-specific forcing addend cannot be silently reused after an odd
    # number of growths has moved the map to the opposite symmetry sector.
    block = ReverseAddSymmetryInnovationBlock.atom(
        (1, 2, 2, 1),
        1,
        source_width=3,
        order=8,
        bits=5,
    )
    with pytest.raises(ValueError, match="paired-sector addend"):
        block.power_block(2)


def test_fixed_real_cyclotomic_germ_roundtrips_aligned_low_views_without_torsion() -> (
    None
):
    rng = random.Random(0xF1EED)
    for bits in (4, 5, 6):
        for width in range(1, 24):
            for _ in range(20):
                half = [rng.randrange(-32, 33) for _ in range((width + 1) // 2)]
                row = _palindrome(half, width)
                views = {
                    order: ReverseAddSymmetryProjection.from_coefficients(
                        row,
                        order=order,
                        bits=bits,
                    ).fixed_coordinates
                    for order in (2, 4, 8)
                }
                germ = FixedRealCyclotomicGerm.from_fixed_views(views, bits=bits)
                assert germ.fixed_views == views
                # Integral reversal-fixed Laurent polynomials never need the
                # modular-only middle torsion coordinate.
                assert views[4][-1] == views[8][-1] == 0


def test_fixed_real_cyclotomic_germ_encodes_exact_divided_value_relations() -> None:
    row = (13, 5, 2, 6, 14, 14, 14, 6, 2, 5, 13)
    views = {
        order: ReverseAddSymmetryProjection.from_coefficients(
            row,
            order=order,
            bits=5,
        ).fixed_coordinates
        for order in (2, 4, 8)
    }
    germ = FixedRealCyclotomicGerm.from_fixed_views(views, bits=5)
    modulus = 32
    # F(0)=R8(0)+2Q(0), F(2)=R8(2)-2Q(2).
    assert views[2][0] == (germ.r0 + 2 * germ.q0) % modulus
    assert views[4][0] == (germ.r0 + 2 * germ.r1 - 2 * germ.q2) % modulus
    assert (germ.q2 - germ.q0) % 2 == 0
    assert germ.description_bits == 17
    assert germ.invisible_kernel_generators() == ((16,), (0, 8), (0, -2, 1))


def test_fixed_real_germ_rejects_modular_fixed_torsion_as_nonintegral_lift() -> None:
    with pytest.raises(ValueError, match="middle torsion"):
        FixedRealCyclotomicGerm.from_fixed_views(
            {2: (0,), 4: (0, 1), 8: (0, 0, 0)},
            bits=5,
        )
