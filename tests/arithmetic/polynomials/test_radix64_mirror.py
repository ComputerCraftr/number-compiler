"""Finite mirror actions and phase-correct folded coefficient extraction."""

from collections.abc import Iterable
from itertools import product

import pytest

from number_compiler.arithmetic.polynomials import arithmetic_tile, radix64_mirror
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    adaptive_square_convolution,
    fold_cyclic,
    fold_negacyclic,
)
from number_compiler.arithmetic.polynomials.radix64_mirror import (
    MirrorCorrActionID,
    compose_mirror_pairs,
    folded_fifth_residue,
    folded_mirror_residue,
    mirror_leaf_action,
)


def test_all_radix64_leaf_pairs_have_exactly_seven_actions() -> None:
    observed: set[MirrorCorrActionID] = set()
    for left, right in product(range(64), repeat=2):
        action = mirror_leaf_action(left, right)
        expected = sum(((left >> i) & 1) * ((right >> i) & 1) for i in range(6))
        assert action.residue == expected
        observed.add(action)
    assert observed == {MirrorCorrActionID(i) for i in range(7)}


def test_all_256_action_compositions_are_extensional_and_canonical() -> None:
    assert len(MirrorCorrActionID) == 16
    for first, second in product(MirrorCorrActionID, repeat=2):
        composed = first.then(second)
        assert composed is MirrorCorrActionID((first.residue + second.residue) % 16)
        for incoming in range(16):
            assert composed.apply(incoming) == second.apply(first.apply(incoming))
        assert first.then(MirrorCorrActionID.ZERO) is first
        for third in MirrorCorrActionID:
            assert composed.then(third) is first.then(second.then(third))


@pytest.mark.parametrize("sign", (-1, 1))
def test_binary_widths_through_ten_match_complete_fold(sign: int) -> None:
    fold = fold_cyclic if sign == 1 else fold_negacyclic
    for width in range(6, 11):
        for coefficients in product((0, 1), repeat=width):
            full, _metrics = adaptive_square_convolution(coefficients)
            result = folded_fifth_residue(coefficients, sign=sign)
            assert result.residue == fold(full, width)[5] % 16
            wrap = sum(
                coefficients[u + 6] * coefficients[width - 1 - u]
                for u in range(width - 6)
            )
            assert result.mirror_action.residue == wrap % 16


@pytest.mark.parametrize("width", range(12, 25))
def test_partial_last_leaf_preserves_reflected_phase(width: int) -> None:
    coefficients = tuple(int(i % 5 in (0, 1, 3)) for i in range(width))
    full, _metrics = adaptive_square_convolution(coefficients)
    for sign, fold in ((1, fold_cyclic), (-1, fold_negacyclic)):
        result = folded_fifth_residue(coefficients, sign=sign)
        assert result.residue == fold(full, width)[5] % 16
        assert result.leaf_pairs == (width + 5) // 6
        assert result.coefficient_reads == 3 * width - 12


def test_aligned_stream_consumes_only_the_action() -> None:
    pairs = ((63, 63), (17, 3), (45, 63), (0, 63))
    first = compose_mirror_pairs(iter(pairs[:2]))
    second = compose_mirror_pairs(iter(pairs[2:]))
    whole = compose_mirror_pairs(iter(pairs))
    assert first.then(second) is whole
    assert compose_mirror_pairs(iter(())) is MirrorCorrActionID.ZERO
    assert mirror_leaf_action(1, 1) is mirror_leaf_action(32, 32)
    for low, sign in product(range(16), (-1, 1)):
        assert (
            folded_mirror_residue(low, whole, sign=sign)
            == (low + sign * sum((a & b).bit_count() for a, b in pairs)) % 16
        )


def test_counted_action_powering_never_reextracts_source_leaves(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    action = mirror_leaf_action(63, 63)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("counted mirror action expanded its source pairs")

    monkeypatch.setattr(radix64_mirror, "mirror_leaf_action", forbidden)
    assert action.power(10**12 + 1) is MirrorCorrActionID.SIX
    for base in MirrorCorrActionID:
        repeated = MirrorCorrActionID.ZERO
        for count in range(33):
            assert base.power(count) is repeated
            repeated = repeated.then(base)


@pytest.mark.parametrize("family", ("fermat", "mersenne"))
def test_production_tile_path_uses_mirror_owner_without_full_square(
    monkeypatch: pytest.MonkeyPatch, family: str
) -> None:
    tile = ArithmeticTile.from_value(ArithmeticTileSpec(family, 17), 0x17355)
    expected = folded_fifth_residue(tile.block.residue, sign=tile.spec.boundary_sign)
    original = radix64_mirror.compose_mirror_pairs
    calls = 0

    def counted(pairs: Iterable[tuple[int, int]]) -> MirrorCorrActionID:
        nonlocal calls
        calls += 1
        return original(pairs)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("mirror observation entered integer/full-square execution")

    monkeypatch.setattr(radix64_mirror, "compose_mirror_pairs", counted)
    monkeypatch.setattr(ArithmeticTile, "residue", property(forbidden))
    monkeypatch.setattr(ArithmeticTile, "_step_with_field", forbidden)
    monkeypatch.setattr(arithmetic_tile, "adaptive_square_convolution", forbidden)
    monkeypatch.setattr(arithmetic_tile, "binary_square_sign_representative", forbidden)
    assert tile.folded_fifth_residue() == expected
    assert calls == 1


@pytest.mark.parametrize("width", (6, 16, 64, 512))
def test_zero_section_has_no_failure_witness_and_dense_work_is_visible(
    width: int,
) -> None:
    for sign in (-1, 1):
        result = folded_fifth_residue((0,) * width, sign=sign)
        assert result.vanishes
        assert result.mirror_action is MirrorCorrActionID.ZERO
        assert result.coefficient_reads == 3 * width - 12


@pytest.mark.parametrize("left,right", ((64, 0), (-1, 0), (True, 0)))
def test_invalid_radix64_ports_are_rejected(left: int, right: int) -> None:
    with pytest.raises(ValueError):
        mirror_leaf_action(left, right)


def test_signed_or_short_tiles_are_outside_the_binary_mirror_chart() -> None:
    for coefficients in ((0,) * 5, (-1, 0, 0, 0, 0, 0), (True,) * 6):
        with pytest.raises(ValueError):
            folded_fifth_residue(coefficients, sign=-1)
