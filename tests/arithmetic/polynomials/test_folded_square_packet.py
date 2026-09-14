"""Exact demanded coefficients, independently compared with the full square."""

from itertools import product

import pytest

from number_compiler.arithmetic.polynomials import arithmetic_tile, digit_convolution
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    adaptive_square_convolution,
    fold_cyclic,
    fold_negacyclic,
)
from number_compiler.arithmetic.polynomials.folded_square_packet import (
    FoldedSquarePacket,
    folded_square_packet,
)


@pytest.mark.parametrize("sign", (-1, 1))
def test_all_binary_polynomials_through_width_eight_match_full_convolution(
    sign: int,
) -> None:
    fold = fold_cyclic if sign == 1 else fold_negacyclic
    for width in range(3, 9):
        for coefficients in product((0, 1), repeat=width):
            full, _metrics = adaptive_square_convolution(coefficients)
            expected = fold(full, width)
            projection = folded_square_packet(coefficients, sign=sign)
            assert projection.packet.canonical_key == (expected[1] % 4, expected[2] % 8)
            assert projection.pair_visits <= width + 2
            assert projection.scalar_products <= projection.pair_visits


@pytest.mark.parametrize("sign", (-1, 1))
def test_signed_coefficients_and_modular_representatives_are_exact(sign: int) -> None:
    fold = fold_cyclic if sign == 1 else fold_negacyclic
    for coefficients in product((-2, -1, 0, 1, 2), repeat=4):
        full, _metrics = adaptive_square_convolution(coefficients)
        expected = fold(full, 4)
        actual = folded_square_packet(coefficients, sign=sign)
        representatives = folded_square_packet(
            tuple(value % 32 for value in coefficients), sign=sign
        )
        assert actual.packet == representatives.packet
        assert actual.packet.canonical_key == (expected[1] % 4, expected[2] % 8)


@pytest.mark.parametrize("family", ("fermat", "mersenne"))
def test_production_tile_observer_does_not_step_decode_or_construct_full_square(
    monkeypatch: pytest.MonkeyPatch, family: str
) -> None:
    tile = ArithmeticTile.from_value(ArithmeticTileSpec(family, 16), 12345)
    expected = folded_square_packet(tile.block.residue, sign=tile.spec.boundary_sign)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("packet observation entered full square or integer reconstruction")

    monkeypatch.setattr(ArithmeticTile, "residue", property(forbidden))
    monkeypatch.setattr(ArithmeticTile, "_step_with_field", forbidden)
    monkeypatch.setattr(arithmetic_tile, "adaptive_square_convolution", forbidden)
    monkeypatch.setattr(arithmetic_tile, "binary_square_sign_representative", forbidden)
    monkeypatch.setattr(digit_convolution, "adaptive_square_convolution", forbidden)
    assert tile.folded_square_packet() == expected


def test_packet_has_exactly_five_bits_without_storing_work_in_identity() -> None:
    packets = {
        FoldedSquarePacket(first, second) for first in range(4) for second in range(8)
    }
    assert len(packets) == 32
    assert sum(packet.vanishes for packet in packets) == 1
    zero = folded_square_packet((0, 0, 0, 0), sign=-1)
    one = folded_square_packet((1, 0, 0, 0), sign=-1)
    assert zero.packet == one.packet == FoldedSquarePacket(0, 0)


@pytest.mark.parametrize("width", (16, 32, 64, 128, 512))
def test_generic_pair_extraction_reports_linear_work(width: int) -> None:
    result = folded_square_packet((1,) * width, sign=-1)
    assert result.pair_visits == width + 1
    assert result.scalar_products == width + 1
    assert result.coefficient_reads == 3 * width + 2


@pytest.mark.parametrize("coefficients,sign", (((1, 0), 1), ((1, 0, 1), 0)))
def test_invalid_projection_shapes_are_rejected(
    coefficients: tuple[int, ...], sign: int
) -> None:
    with pytest.raises(ValueError):
        folded_square_packet(coefficients, sign=sign)


def test_boolean_coefficients_are_not_exact_integer_ports() -> None:
    with pytest.raises(TypeError):
        folded_square_packet((True, 0, 1), sign=1)
