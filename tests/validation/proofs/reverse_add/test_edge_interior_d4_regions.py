"""Bounded checks for the research-only edge/interior C2 -> C4 rules."""

from collections.abc import Iterable

import pytest

from devtools.experiments.reverse_add.edge_interior_d4_regions import (
    FiniteCarryRegion,
    FiniteInterval,
    construct_edge_interior_d4,
)
from number_compiler.arithmetic.fields.radial_innovation import RadialMultiplier
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
    CyclotomicDigitBlock,
)
from number_compiler.resources.ledger import ResourceLedger


def _trim(value: list[int]) -> list[int]:
    while value and value[-1] == 0:
        value.pop()
    return value


def _add(*values: list[int]) -> list[int]:
    width = max((len(value) for value in values), default=0)
    return _trim(
        [
            sum(value[index] if index < len(value) else 0 for value in values)
            for index in range(width)
        ]
    )


def _scale(coefficient: int, value: list[int]) -> list[int]:
    return _trim([coefficient * item for item in value])


def _shift(value: list[int]) -> list[int]:
    return [0, *value] if value else []


def _hasse(value: list[int]) -> list[int]:
    return _add(value, _shift(value))


def _reflect(value: list[int], degree: int) -> list[int]:
    return _trim(
        [
            value[degree - index] if degree - index < len(value) else 0
            for index in range(degree + 1)
        ]
    )


def _correction(carry: list[int]) -> list[int]:
    return _add(_shift(carry), _scale(-10, carry))


def _beta(correction: list[int], degree: int) -> list[int]:
    return _add(correction, _reflect(correction, degree))


def _literal_step(
    pair: list[int], base: int = 10
) -> tuple[list[int], list[int], list[int]]:
    carry = [0]
    digits: list[int] = []
    for coefficient in pair:
        next_carry, digit = divmod(coefficient + carry[-1], base)
        carry.append(next_carry)
        digits.append(digit)
    if carry[-1]:
        digits.append(carry[-1])
    return carry, digits, _add(digits, list(reversed(digits)))


def _indicator(region: FiniteCarryRegion) -> list[int]:
    return [int(region.contains(index)) for index in range(region.extent)]


def _negacyclic_atom(coefficients: list[int]) -> list[int]:
    """Independent reduction modulo Phi_16=z^8+1 for bounded references."""
    result = [0] * 8
    for index, coefficient in enumerate(coefficients):
        result[index % 8] += (-1 if (index // 8) % 2 else 1) * coefficient
    return [coefficient % (1 << 16) for coefficient in result]


def _coefficient(value: list[int], index: int) -> int:
    return value[index] if 0 <= index < len(value) else 0


def _assert_same_polynomial(left: list[int], right: list[int]) -> None:
    for index in range(-2, max(len(left), len(right)) + 2):
        assert _coefficient(left, index) == _coefficient(right, index)


def _initial_innovations(extent: int) -> tuple[list[int], list[int]]:
    q0 = [0, *([1] * (extent - 2))]
    e0 = _correction(q0)
    beta0 = _beta(e0, extent - 1)
    q1 = [1] * extent
    e1 = _correction(q1)
    beta1 = _beta(e1, extent)
    return _add(_hasse(beta0), beta1), _add(beta0, e1)


def _all_parameters() -> Iterable[tuple[int, int, int]]:
    for extent in range(3, 13):
        for edge in range(5, 9):
            for interior in range(8, 10):
                yield extent, edge, interior


@pytest.mark.parametrize(("extent", "edge", "interior"), tuple(_all_parameters()))
def test_d4_regions_and_arrows_match_four_independent_forward_steps(
    extent: int,
    edge: int,
    interior: int,
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    clause = construct_edge_interior_d4(
        arena,
        source_label=41,
        extent=extent,
        edge=edge,
        interior_digit=interior,
    )
    source = [edge, *([2 * interior] * (extent - 2)), edge]
    pair = source
    steps: list[tuple[list[int], list[int], list[int]]] = []
    for _ in range(4):
        step = _literal_step(pair)
        steps.append(step)
        pair = step[2]
    carry2, digits2, pair3 = steps[2]
    carry3, digits3, pair4 = steps[3]
    q2 = _indicator(clause.q2_region)
    q3 = _indicator(clause.q3_region)

    assert q2 == carry2[1:]
    assert q3 == carry3[1:]
    assert clause.growth2 == carry2[-1] == 0
    assert clause.growth3 == carry3[-1] == int(edge >= 7)

    b2, _output1_innovation = _initial_innovations(extent)
    e2 = _correction(q2)
    beta2 = _beta(e2, extent)
    b3 = _add(_scale(2, b2), beta2)
    symbolic_output2 = _add(_scale(2, _hasse(source)), b2, e2)
    symbolic_pair3 = _add(_scale(4, _hasse(source)), b3)

    e3 = _correction(q3)
    beta3 = _beta(e3, extent + clause.growth3)
    b4 = _add(_hasse(b3) if clause.growth3 else _scale(2, b3), beta3)
    radial4 = (
        _scale(4, _hasse(_hasse(source)))
        if clause.growth3
        else _scale(8, _hasse(source))
    )
    symbolic_output3 = _add(_scale(4, _hasse(source)), b3, e3)
    symbolic_pair4 = _add(radial4, b4)

    _assert_same_polynomial(symbolic_output2, digits2)
    _assert_same_polynomial(symbolic_pair3, pair3)
    _assert_same_polynomial(symbolic_output3, digits3)
    _assert_same_polynomial(symbolic_pair4, pair4)

    q0 = [0, *([1] * (extent - 2))]
    q1 = [1] * extent
    atoms = {
        clause.d2.q0_semantic: _negacyclic_atom(q0),
        clause.d2.q1_semantic: _negacyclic_atom(q1),
        clause.q2_semantic: _negacyclic_atom(q2),
        clause.q3_semantic: _negacyclic_atom(q3),
    }
    expected_actions = (
        (clause.output2, RadialMultiplier(1, 1), _add(b2, e2)),
        (clause.pair3, RadialMultiplier(2, 1), b3),
        (clause.output3, RadialMultiplier(2, 1), _add(b3, e3)),
        (
            clause.pair4,
            RadialMultiplier(2, 2) if clause.growth3 else RadialMultiplier(3, 1),
            b4,
        ),
    )
    for action, multiplier, innovation in expected_actions:
        projected = arena.project_cyclotomic(
            action,
            order=16,
            bits=16,
            atoms=atoms,
        )
        expected = CyclotomicDigitBlock.from_coefficients(
            innovation,
            order=16,
            modulus=1 << 16,
        )
        assert action.multiplier == multiplier
        assert projected.innovation == expected.residue


@pytest.mark.parametrize(
    ("extent", "edge", "interior", "q2", "q3"),
    (
        (3, 5, 8, (), ((1, 3),)),
        (3, 6, 9, ((1, 3),), ()),
        (3, 7, 8, (), ((0, 4),)),
        (3, 7, 9, ((1, 3),), ((0, 1), (3, 4))),
        (4, 7, 8, ((1, 2), (3, 4)), ((0, 1), (2, 3), (4, 5))),
        (5, 6, 9, ((1, 5),), ((2, 4),)),
        (6, 5, 8, ((3, 5),), ((1, 3), (5, 6))),
    ),
)
def test_width_and_seam_cases_are_explicit(
    extent: int,
    edge: int,
    interior: int,
    q2: tuple[tuple[int, int], ...],
    q3: tuple[tuple[int, int], ...],
) -> None:
    clause = construct_edge_interior_d4(
        SymbolicInnovationArena(ResourceLedger()),
        source_label=0,
        extent=extent,
        edge=edge,
        interior_digit=interior,
    )

    assert tuple((item.start, item.stop) for item in clause.q2_region.intervals) == q2
    assert tuple((item.start, item.stop) for item in clause.q3_region.intervals) == q3


def test_d4_construction_never_observes_a_future_coefficient(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("research construction evaluated a future coefficient")

    monkeypatch.setattr(SymbolicInnovationArena, "project_cyclotomic", forbidden)
    monkeypatch.setattr(FiniteCarryRegion, "contains", forbidden)
    counts: list[int] = []
    for extent in (3, 17, 10**6):
        arena = SymbolicInnovationArena(ResourceLedger())
        clause = construct_edge_interior_d4(
            arena,
            source_label=8,
            extent=extent,
            edge=5,
            interior_digit=8,
        )
        counts.append(arena.node_count)
        assert clause.production_admitted is False
        assert clause.d2.production_admitted is False
        with pytest.raises(ValueError, match="not authenticated"):
            clause.require_production_admission()

    assert counts[0] == counts[1] == counts[2]


def test_interval_atoms_cannot_hide_an_unbounded_position_word() -> None:
    with pytest.raises(ValueError, match="at most three"):
        FiniteCarryRegion(100, tuple(FiniteInterval(i, i + 1) for i in (0, 2, 4, 6)))
    with pytest.raises(ValueError, match="touch"):
        FiniteCarryRegion(10, (FiniteInterval(1, 2), FiniteInterval(2, 3)))
    region = FiniteCarryRegion(10, (FiniteInterval(1, 3),))
    object.__setattr__(region, "intervals", [FiniteInterval(1, 3)])
    with pytest.raises(TypeError, match="immutable"):
        region.__post_init__()
