import pytest

from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
    SquareTileAction,
    SquarePrecisionMap,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    binary_square_sign_representative,
    cyclic_binary_square_add_projection,
    negacyclic_binary_square_projection,
)
from number_compiler.arithmetic.fields.morphism_core import (
    binary_power_composition_count,
)


def test_square_tiles_apply_exact_cyclic_and_negacyclic_boundary_arithmetic() -> None:
    fermat = ArithmeticTileSpec.fermat(4)
    assert [
        ArithmeticTile.from_value(fermat, value).step().tile.residue
        for value in (16, 17, 18)
    ] == [1, 0, 1]

    mersenne = ArithmeticTileSpec.mersenne(5)
    assert [
        ArithmeticTile.from_value(mersenne, value).step().tile.residue
        for value in (30, 31, 32)
    ] == [30, 29, 30]


def test_repeated_tile_steps_equal_direct_special_recurrences() -> None:
    for spec, start, steps in (
        (ArithmeticTileSpec.fermat(8), 3, 7),
        (ArithmeticTileSpec.mersenne(7), 4, 5),
    ):
        expected = start % spec.modulus
        for _ in range(steps):
            expected = (expected * expected + spec.addend) % spec.modulus
        result = ArithmeticTile.from_value(spec, start).run(steps)
        assert result.residue == expected
        assert result.primitive_steps == steps
        assert result.metrics.scheduler_compositions == 0
        assert result.metrics.scalar_multiplications > 0


def test_tile_state_is_the_full_boundary_cyclotomic_digit_block() -> None:
    fermat = ArithmeticTile.from_value(ArithmeticTileSpec.fermat(4), 16)
    assert fermat.block.factor == (1, 0, 0, 0, 1)
    assert fermat.block.residue == (fermat.spec.precision.modulus - 1, 0, 0, 0)
    assert fermat.residue == 16

    mersenne = ArithmeticTile.from_value(ArithmeticTileSpec.mersenne(5), 7)
    assert mersenne.block.factor == (
        mersenne.spec.precision.modulus - 1,
        0,
        0,
        0,
        0,
        1,
    )
    assert mersenne.block.degree == mersenne.spec.width
    assert "residue" not in mersenne.spec.canonical_key
    assert mersenne.spec.precision.canonical_key[0] == "square-forward-precision"
    assert not hasattr(mersenne.spec.precision, "inverse_three")

    angular = fermat.angular_view(modulus=5)
    assert angular.factor is None
    assert angular.order == fermat.spec.angular_order
    assert angular.length == fermat.spec.width
    assert angular is not fermat.block


def test_tile_rejects_noncanonical_equal_value_digit_blocks() -> None:
    cyclic = ArithmeticTileSpec.mersenne(5)
    with pytest.raises(ValueError, match="noncanonical"):
        ArithmeticTile(cyclic, cyclic.block((1, 1, 1, 1, 1)))
    fermat = ArithmeticTileSpec.fermat(4)
    with pytest.raises(ValueError, match="noncanonical"):
        ArithmeticTile(fermat, fermat.block((2, 0, 0, 0)))


def test_square_precision_is_minimal_and_rejects_collatz_inverse_style_parameters() -> (
    None
):
    for invalid in (0, -1, 1.5):
        with pytest.raises(ValueError):
            SquarePrecisionMap(invalid)  # type: ignore[arg-type]
    for spec in (ArithmeticTileSpec.fermat(64), ArithmeticTileSpec.mersenne(64)):
        bound = 2 * (spec.width + abs(spec.addend) + 1)
        assert spec.precision.modulus > bound
        assert spec.precision.modulus // 2 <= bound


def test_shared_tile_does_not_call_family_specific_projection_entrypoints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.polynomials.digit_convolution as legacy

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError((args, kwargs))

    monkeypatch.setattr(legacy, "cyclic_binary_square_add_projection", forbidden)
    monkeypatch.setattr(legacy, "negacyclic_binary_square_projection", forbidden)
    mersenne = ArithmeticTile.from_value(ArithmeticTileSpec.mersenne(11), 4).run(9)
    expected = 4
    for _ in range(9):
        expected = (expected * expected - 2) % 2047
    assert mersenne.residue == expected
    assert (
        ArithmeticTile.from_value(ArithmeticTileSpec.fermat(16), 3).run(15).residue
        == 65536
    )


def test_shared_square_action_composes_depth_without_duplicate_span_storage() -> None:
    for family, modulus, start, span in (
        ("fermat", 257, 3, 7),
        ("mersenne", 127, 4, 5),
    ):
        action = SquareTileAction.atom(family).power_block(span)
        expected = start
        for _ in range(span):
            expected = (
                expected * expected if family == "fermat" else expected * expected - 2
            ) % modulus
        assert action.span == action.endpoint_power.depth == span
        assert "span" not in action.__dataclass_fields__
        assert action.compositions == binary_power_composition_count(span)
        assert action.apply(start, modulus) == expected


def test_shared_kernel_exhaustively_matches_independent_family_projections() -> None:
    for width in range(2, 9):
        for family in ("fermat", "mersenne"):
            spec = getattr(ArithmeticTileSpec, family)(width)
            for value in range(spec.modulus):
                representative = binary_square_sign_representative(
                    value, width, spec.boundary_sign
                )
                reference = (
                    negacyclic_binary_square_projection(representative, width)
                    if family == "fermat"
                    else cyclic_binary_square_add_projection(representative, width, -2)
                )
                got = ArithmeticTile.from_value(spec, value).step()
                assert got.tile.residue == reference.residue
                assert (
                    got.normalization.canonical_key
                    == reference.normalization.canonical_key
                )
                assert got.convolution == reference.convolution
                assert got.naive_scalar_products == reference.naive_scalar_products


def test_boundary_consumer_action_is_demanded_from_the_folded_product() -> None:
    step = ArithmeticTile.from_value(ArithmeticTileSpec.fermat(8), 197).step()
    action = step.boundary_action(incoming_min=-2, incoming_max=2)
    assert action.outgoing == tuple(
        step.normalization.block.outgoing_carry(carry) for carry in range(-2, 3)
    )
    assert action.canonical_key not in step.tile.canonical_key


def test_ordinary_step_does_not_scan_a_demanded_carry_interval(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.polynomials.arithmetic_tile as tile_module

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError((args, kwargs))

    monkeypatch.setattr(tile_module, "normalization_carry_boundaries", forbidden)
    step = ArithmeticTile.from_value(ArithmeticTileSpec.mersenne(7), 4).step()
    assert step.tile.residue == 14
