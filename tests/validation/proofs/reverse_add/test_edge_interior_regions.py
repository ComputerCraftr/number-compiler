"""Bounded evidence for the edge/interior symbolic D2 chamber."""

from dataclasses import replace

import pytest

from devtools.experiments.reverse_add.edge_interior_regions import (
    construct_edge_interior_d2,
)
from number_compiler.arithmetic.fields.radial_innovation import RadialMultiplier
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
    CyclotomicDigitBlock,
)
from number_compiler.resources.ledger import ResourceLedger


def _assert_padded_equal(actual: list[int], expected: list[int]) -> None:
    for index in range(-2, len(expected) + 2):
        want = expected[index] if 0 <= index < len(expected) else 0
        got = actual[index] if 0 <= index < len(actual) else 0
        assert got == want


def _indicator(start: int, stop: int) -> list[int]:
    result = [0] * stop
    for index in range(start, stop):
        result[index] = 1
    return result


def _add(left: list[int], right: list[int]) -> list[int]:
    width = max(len(left), len(right))
    return [
        (left[i] if i < len(left) else 0) + (right[i] if i < len(right) else 0)
        for i in range(width)
    ]


def _shift(value: list[int]) -> list[int]:
    return [0, *value]


def _scale(coefficient: int, value: list[int]) -> list[int]:
    return [coefficient * item for item in value]


def _literal_step(
    pair: list[int], base: int = 10
) -> tuple[list[int], list[int], list[int]]:
    carry = [0]
    digits = []
    for coefficient in pair:
        total = coefficient + carry[-1]
        next_carry, digit = divmod(total, base)
        carry.append(next_carry)
        digits.append(digit)
    if carry[-1]:
        digits.append(carry[-1])
    return carry, digits, _add(digits, list(reversed(digits)))


@pytest.mark.parametrize("extent", (3, 4, 7))
def test_symbolic_d2_innovation_matches_independent_polynomial_arithmetic(
    extent: int,
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    clause = construct_edge_interior_d2(
        arena,
        source_label=17,
        extent=extent,
        edge=7,
        interior_digit=9,
    )
    q0 = _indicator(1, extent - 1)
    q1 = _indicator(0, extent)
    e0 = _add(_shift(q0), _scale(-10, q0))
    beta0 = _add(e0, list(reversed(e0)))
    e1 = _add(_shift(q1), _scale(-10, q1))
    beta1 = _scale(-9, _add(q1, _shift(q1)))
    expected = _add(_add(beta0, _shift(beta0)), beta1)
    expected_output_innovation = _add(beta0, e1)
    q0_residue = [*q0, *([0] * (8 - len(q0)))]
    q1_residue = [*q1, *([0] * (8 - len(q1)))]
    projected = arena.project_cyclotomic(
        clause.action,
        order=16,
        bits=16,
        atoms={
            clause.q0_semantic: q0_residue,
            clause.q1_semantic: q1_residue,
        },
    )
    block = CyclotomicDigitBlock.from_coefficients(expected, order=16, modulus=1 << 16)
    output_projected = arena.project_cyclotomic(
        clause.output_action,
        order=16,
        bits=16,
        atoms={
            clause.q0_semantic: q0_residue,
            clause.q1_semantic: q1_residue,
        },
    )
    output_block = CyclotomicDigitBlock.from_coefficients(
        expected_output_innovation, order=16, modulus=1 << 16
    )

    assert projected.innovation == block.residue
    assert clause.action.multiplier == RadialMultiplier(1, 1)
    assert output_projected.innovation == output_block.residue
    assert clause.output_action.multiplier == RadialMultiplier(1, 0)
    assert clause.threshold.edge_minimum == 11
    assert clause.threshold.width_three_center_minimum == 12
    assert clause.threshold.shoulder_minimum == 13
    assert clause.threshold.bulk_minimum == 14


def test_symbolic_construction_size_is_independent_of_extent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("symbolic construction evaluated a future coefficient")

    monkeypatch.setattr(SymbolicInnovationArena, "project_cyclotomic", forbidden)
    counts = []
    for extent in (3, 17, 10**6):
        arena = SymbolicInnovationArena(ResourceLedger())
        construct_edge_interior_d2(
            arena,
            source_label=4,
            extent=extent,
            edge=5,
            interior_digit=8,
        )
        counts.append(arena.node_count)

    assert counts[0] == counts[1] == counts[2]


def test_parameter_region_matches_two_independent_forward_steps_exhaustively() -> None:
    for extent in range(3, 13):
        for edge in range(5, 9):
            for interior in range(8, 10):
                arena = SymbolicInnovationArena(ResourceLedger())
                clause = construct_edge_interior_d2(
                    arena,
                    source_label=31,
                    extent=extent,
                    edge=edge,
                    interior_digit=interior,
                )
                source = [edge, *([2 * interior] * (extent - 2)), edge]
                carry0, _digits0, pair1 = _literal_step(source)
                carry1, digits1, pair2 = _literal_step(pair1)
                q0 = [int(clause.q0_region.contains(i, extent)) for i in range(extent)]
                q1 = [int(clause.q1_region.contains(i, extent)) for i in range(extent)]

                assert q0 == carry0[1:]
                assert q1 == carry1[1:]
                assert carry0[-1] == 0
                assert carry1[-1] == 1

                # Q0's declared support ends at m-2; omit its known trailing zero
                # so reversal is R_(m-1), matching the cylinder chart.
                q0_polynomial = q0[:-1]
                e0 = _add(_shift(q0_polynomial), _scale(-10, q0_polynomial))
                beta0 = _add(e0, list(reversed(e0)))
                beta1 = _scale(-9, _add(q1, _shift(q1)))
                b2 = _add(_add(beta0, _shift(beta0)), beta1)
                e1 = _add(_shift(q1), _scale(-10, q1))
                symbolic_digits1 = _add(_scale(2, source), _add(beta0, e1))
                radial = _scale(2, _add(source, _shift(source)))
                symbolic_pair2 = _add(radial, b2)
                _assert_padded_equal(symbolic_digits1, digits1)
                _assert_padded_equal(symbolic_pair2, pair2)


@pytest.mark.parametrize(
    ("extent", "edge", "interior"),
    ((2, 7, 9), (3, 4, 9), (3, 9, 9), (3, 7, 7)),
)
def test_constructor_rejects_parameters_outside_proved_region(
    extent: int, edge: int, interior: int
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())

    with pytest.raises(ValueError, match="leave the edge/interior"):
        construct_edge_interior_d2(
            arena,
            source_label=0,
            extent=extent,
            edge=edge,
            interior_digit=interior,
        )


def test_formal_source_label_never_claims_production_admission() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    first = construct_edge_interior_d2(
        arena,
        source_label=1,
        extent=3,
        edge=7,
        interior_digit=9,
    )
    spoof = construct_edge_interior_d2(
        arena,
        source_label=2,
        extent=3,
        edge=7,
        interior_digit=9,
    )

    assert first.q0_semantic != spoof.q0_semantic
    assert first.production_admitted is spoof.production_admitted is False
    with pytest.raises(ValueError, match="not authenticated"):
        first.require_production_admission()


def test_threshold_certificate_recomputes_fixed_chamber_bounds() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    clause = construct_edge_interior_d2(
        arena,
        source_label=0,
        extent=3,
        edge=7,
        interior_digit=9,
    )

    forged = type(clause.threshold)(100, 100, 100, 100)
    with pytest.raises(ValueError, match="not derived"):
        forged.validate(clause.predicate)

    for widened in (
        replace(clause.predicate, minimum_extent=1),
        replace(clause.predicate, edge_high=10),
        replace(clause.predicate, interior_high=10),
    ):
        with pytest.raises(ValueError, match="fixed chamber"):
            clause.threshold.validate(widened)

    mistyped = replace(clause.predicate)
    object.__setattr__(mistyped, "minimum_extent", 3.0)
    with pytest.raises(TypeError, match="exact integers"):
        clause.threshold.validate(mistyped)
