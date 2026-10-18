"""Independent finite-set checks for shared affine interval/coset transport."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.integer_cylinder import IntegerCylinder


@pytest.mark.parametrize("lower,upper", ((-17, 27), (1, 1), (4, 41)))
@pytest.mark.parametrize("modulus", (1, 2, 6, 15))
def test_cylinder_intersections_equal_literal_sets(
    lower: int, upper: int, modulus: int
) -> None:
    source = IntegerCylinder(lower, upper, lower % modulus, modulus)
    expected = {x for x in range(lower, upper + 1) if x % modulus == lower % modulus}
    assert source.enumerated() == tuple(sorted(expected))
    assert source.count == len(expected)
    for r in range(4):
        joined = source.intersect_congruence(r, 4)
        selected = {x for x in expected if x % 4 == r}
        assert (set(joined.enumerated() or ()) if joined else set()) == selected
    interval = source.intersect_interval(0, 12)
    selected = expected & set(range(13))
    assert (set(interval.enumerated() or ()) if interval else set()) == selected


@pytest.mark.parametrize("gain,offset,denominator", ((3, 1, 2), (9, -5, 4), (3, 0, 1)))
def test_affine_transport_preserves_full_stride_and_count(
    gain: int, offset: int, denominator: int
) -> None:
    # The first odd source and stride make every one of these maps integral.
    source = IntegerCylinder(1, 145, 1, 24)
    image = source.affine_image(gain, offset, denominator)
    expected = tuple(
        (gain * x + offset) // denominator for x in source.enumerated() or ()
    )
    assert image.enumerated() == expected
    assert image.modulus == gain * source.modulus // denominator
    assert image.count == source.count
    if gain == 3 and denominator == 1:
        assert not image.contains(image.first + source.modulus)


def test_affine_transport_charges_operand_bits_before_success_or_refusal() -> None:
    source = IntegerCylinder(1, 145, 1, 24)
    charges: list[int] = []
    source.affine_image(3, 1, 2, charge_bits=charges.append)
    expected = sum(value.bit_length() for value in (1, 145, 1, 24, 3, 1, 2))
    assert charges == [expected]

    before = source
    with pytest.raises(ValueError, match="positive"):
        source.affine_image(0, 1, 2, charge_bits=charges.append)
    assert source == before
    assert charges[-1] == sum(value.bit_length() for value in (1, 145, 1, 24, 0, 1, 2))


def test_affine_transport_charge_refusal_does_not_mutate_source() -> None:
    source = IntegerCylinder(1, 145, 1, 24)
    before = source
    received: list[int] = []

    def refuse(bits: int) -> None:
        received.append(bits)
        raise RuntimeError("ledger budget exhausted")

    with pytest.raises(RuntimeError, match="budget exhausted"):
        source.affine_image(3, 1, 2, charge_bits=refuse)
    assert received
    assert source == before


def test_chronological_affine_composition_keeps_exact_fiber() -> None:
    source = IntegerCylinder(1, 145, 1, 24)
    sequential = source.affine_image(3, 1, 2).affine_image(5, 2, 3)
    direct = source.affine_image(15, 9, 6)
    assert sequential == direct


@pytest.mark.parametrize("gain,offset,denominator", ((3, 0, 2), (3, 1, 8), (0, 0, 1)))
def test_nonintegral_or_nonincreasing_actions_refuse(
    gain: int, offset: int, denominator: int
) -> None:
    with pytest.raises(ValueError):
        IntegerCylinder(1, 145, 1, 6).affine_image(gain, offset, denominator)


def test_geometry_does_not_allocate_a_large_fiber() -> None:
    source = IntegerCylinder(1, 10**100, 1, 2)
    assert source.enumerated(64) is None
    assert source.intersect_congruence(0, 2) is None
    assert source.intersect_interval(2, 2) is None
    assert not source.contains(True)
    with pytest.raises(TypeError):
        IntegerCylinder(True, 10, 0, 1)
    with pytest.raises(ValueError):
        IntegerCylinder(2, 2, 1, 2)
